/**
 * Provides classes and predicates for defining flow summaries.
 */

private import cpp as Cpp
private import codeql.dataflow.internal.FlowSummaryImpl
private import codeql.dataflow.internal.AccessPathSyntax as AccessPath
private import semmle.code.cpp.ir.dataflow.internal.DataFlowPrivate
private import semmle.code.cpp.ir.dataflow.internal.DataFlowNodes
private import semmle.code.cpp.ir.dataflow.internal.DataFlowUtil
private import semmle.code.cpp.ir.dataflow.internal.DataFlowImplSpecific as DataFlowImplSpecific
private import semmle.code.cpp.dataflow.ExternalFlow
private import semmle.code.cpp.ir.IR

/**
 * Decodes an argument / parameter position string, for example the `0` in `Argument[0]`.
 * Supports ranges (`Argument[x..y]`), qualifiers (`Argument[-1]`), indirections
 * (`Argument[*x]`) and combinations (such as `Argument[**0..1]`).
 */
bindingset[argString]
SourcePosition decodePosition(string argString) {
  exists(int indirection, string posString, int pos |
    argString = repeatStars(indirection) + posString and
    pos = AccessPath::parseInt(posString) and
    (
      pos >= 0 and indirection = 0 and result = TDirectPosition(pos)
      or
      pos >= 0 and indirection > 0 and result = TIndirectionPosition(pos, indirection)
      or
      // `Argument[-1]` / `Parameter[-1]` is the qualifier object `*this`, not the `this` pointer itself.
      pos = -1 and result = TIndirectionPosition(pos, indirection + 1)
    )
  )
}

module Input implements InputSig<Location, DataFlowImplSpecific::CppDataFlow> {
  class SummarizedCallableBase = Function;

  abstract private class SourceSinkBase extends Element {
    /** Gets the call associated with this element, if any. */
    CallInstruction asCall() { none() }

    /**
     * Holds if `(call, i)` represents an argument associated with this
     * element, if any.
     */
    predicate asArgument(CallInstruction call, int i) { none() }

    /** Gets the parameter associated with this element, if any. */
    Parameter asParameter() { none() }

    /** Gets the enclosing function of this element. */
    abstract Declaration getEnclosingFunction();
  }

  abstract class SourceBase extends SourceSinkBase { }

  abstract class SinkBase extends SourceSinkBase { }

  private class SourceSinkCall extends SourceBase, SinkBase instanceof Call {
    CallInstruction call;

    SourceSinkCall() { call.getUnconvertedResultExpression() = this }

    final override CallInstruction asCall() { result = call }

    final override Declaration getEnclosingFunction() { result = Call.super.getEnclosingFunction() }
  }

  private class Argument extends Expr {
    CallInstruction call;
    int i;

    Argument() { call.getArgument(i).getUnconvertedResultExpression() = this }

    CallInstruction getCall() { result = call }

    int getIndex() { result = i }
  }

  private class SourceSinkArgument extends SourceBase, SinkBase instanceof Argument {
    final override predicate asArgument(CallInstruction call, int i) {
      call = Argument.super.getCall() and
      Argument.super.getIndex() = i
    }

    final override Declaration getEnclosingFunction() {
      result = Argument.super.getEnclosingFunction()
    }
  }

  private class SourceSinkParameter extends SourceBase, SinkBase instanceof Parameter {
    Function f;

    SourceSinkParameter() { f = Parameter.super.getFunction() }

    final override Parameter asParameter() { result = this }

    final override Declaration getEnclosingFunction() { result = f }
  }

  class FlowSummaryCallBase = CallInstruction;

  predicate callableFromSource(SummarizedCallableBase c) { exists(c.getBlock()) }

  FlowSummaryCallBase getASourceCall(SummarizedCallableBase sc) {
    result.getStaticCallTarget() = sc
  }

  DataFlowCallable getSummarizedCallableAsDataFlowCallable(SummarizedCallableBase c) {
    result.asSummarizedCallable() = c
  }

  DataFlowCallable getSourceCallEnclosingCallable(FlowSummaryCallBase call) {
    result.asSourceCallable() = call.getEnclosingFunction()
  }

  ArgumentPosition callbackSelfParameterPosition() { result = TDirectPosition(-1) }

  ReturnKind getStandardReturnValueKind() { result = getReturnValueKind("") }

  ReturnKind getReturnValueKind(string arg) {
    arg = repeatStars(result.(NormalReturnKind).getIndirectionIndex())
  }

  ParameterPosition getFlowSummaryParameterPosition(ReturnKind rk) {
    result = TFlowSummaryPosition(rk)
  }

  string encodeParameterPosition(ParameterPosition pos) { result = pos.toString() }

  string encodeArgumentPosition(ArgumentPosition pos) { result = pos.toString() }

  string encodeReturn(ReturnKind rk, string arg) {
    rk != getStandardReturnValueKind() and
    result = "ReturnValue" and
    arg = repeatStars(rk.(NormalReturnKind).getIndirectionIndex())
  }

  bindingset[namespace, type, base]
  private string formatQualifiedName(string namespace, string type, string base) {
    if namespace = ""
    then result = type + "::" + base
    else result = namespace + "::" + type + "::" + base
  }

  string encodeContent(ContentSet cs, string arg) {
    exists(FieldContent c, string namespace, string type, string base |
      cs.isSingleton(c) and
      // FieldContent indices have 0 for the address, 1 for content, so we need to subtract one.
      result = "Field" and
      c.getField().hasQualifiedName(namespace, type, base)
    |
      arg = repeatStars(c.getIndirectionIndex() - 1) + formatQualifiedName(namespace, type, base)
      or
      // TODO: This disjunct can be removed once we stop supporting unqualified field names.
      arg = repeatStars(c.getIndirectionIndex() - 1) + base
    )
    or
    exists(ElementContent ec |
      cs.isSingleton(ec) and
      result = "Element" and
      arg = repeatStars(ec.getIndirectionIndex() - 1)
    )
  }

  string encodeWithoutContent(ContentSet c, string arg) {
    // used for type tracking, not currently used in C/C++.
    none()
  }

  string encodeWithContent(ContentSet c, string arg) {
    // used for type tracking, not currently used in C/C++.
    none()
  }

  bindingset[token]
  ParameterPosition decodeUnknownParameterPosition(AccessPath::AccessPathTokenBase token) {
    token.getName() = "Argument" and
    result = decodePosition(token.getAnArgument())
  }

  bindingset[token]
  ArgumentPosition decodeUnknownArgumentPosition(AccessPath::AccessPathTokenBase token) {
    token.getName() = "Parameter" and
    result = decodePosition(token.getAnArgument())
  }
}

private import Make<Location, DataFlowImplSpecific::CppDataFlow, Input> as Impl

private module StepsInput implements Impl::Private::StepsInputSig {
  Impl::Private::SummaryNode getSummaryNode(Node n) {
    result = n.(FlowSummaryNode).getSummaryNode()
  }

  DataFlowCall getACall(Public::SummarizedCallable sc) {
    result.getStaticCallTarget().getUnderlyingCallable() = sc
  }

  Node getSourceOutNode(Input::FlowSummaryCallBase call, ReturnKind rk) {
    exists(IndirectReturnOutNode out | result = out |
      out.getCallInstruction() = call and
      pragma[only_bind_out](rk.(NormalReturnKind).getIndirectionIndex()) =
        pragma[only_bind_out](out.getIndirectionIndex())
    )
  }

  DataFlowCallable getSourceNodeEnclosingCallable(Input::SourceBase source) {
    result.asSourceCallable() = source.getEnclosingFunction()
  }

  Node getSourceNode(Input::SourceBase source, Impl::Private::SummaryComponentStack s) {
    exists(ReturnKind rk, DataFlowCall call |
      s.head() = Impl::Private::SummaryComponent::return(rk) and
      source.asCall() = call.asCallInstruction() and
      result = getAnOutNode(call, rk)
    )
    or
    exists(Position pos, DataFlowCallable callable |
      s.head() = Impl::Private::SummaryComponent::parameter(pos) and
      result.(ParameterNode).isParameterOf(callable, pos) and
      source.asParameter().getFunction() = callable.asSourceCallable() and
      source.asParameter().getIndex() = pos.getArgumentIndex()
    )
    or
    exists(Position pos, DataFlowCall call |
      result.(PostUpdateNode).getPreUpdateNode().(ArgumentNode).argumentOf(call, pos) and
      s.headOfSingleton() = Impl::Private::SummaryComponent::argument(pos) and
      source.asArgument(call.asCallInstruction(), pos.getArgumentIndex())
    )
  }

  Node getSinkNode(Input::SinkBase sink, Impl::Private::SummaryComponent sc) { none() }
}

module SourceSinkInterpretationInput implements
  Impl::Private::External::SourceSinkInterpretationInputSig
{
  class Element = Cpp::Element;

  class SourceOrSinkElement = Element;

  /**
   * Holds if an external source specification exists for `e` with output specification
   * `output`, kind `kind`, and provenance `provenance`.
   */
  predicate sourceElement(
    SourceOrSinkElement e, string output, string kind, Public::Provenance provenance, string model
  ) {
    exists(
      string namespace, string type, boolean subtypes, string name, string signature, string ext
    |
      sourceModel(namespace, type, subtypes, name, signature, ext, output, kind, provenance, model) and
      e = interpretElement(namespace, type, subtypes, name, signature, ext)
    )
  }

  /**
   * Holds if an external sink specification exists for `e` with input specification
   * `input`, kind `kind` and provenance `provenance`.
   */
  predicate sinkElement(
    SourceOrSinkElement e, string input, string kind, Public::Provenance provenance, string model
  ) {
    exists(
      string package, string type, boolean subtypes, string name, string signature, string ext
    |
      sinkModel(package, type, subtypes, name, signature, ext, input, kind, provenance, model) and
      e = interpretElement(package, type, subtypes, name, signature, ext)
    )
  }

  predicate barrierElement(
    Element e, string output, string kind, Public::Provenance provenance, string model
  ) {
    exists(
      string namespace, string type, boolean subtypes, string name, string signature, string ext
    |
      barrierModel(namespace, type, subtypes, name, signature, ext, output, kind, provenance, model) and
      e = interpretElement(namespace, type, subtypes, name, signature, ext)
    )
  }

  predicate barrierGuardElement(
    Element e, string input, Public::AcceptingValue acceptingValue, string kind,
    Public::Provenance provenance, string model
  ) {
    exists(
      string package, string type, boolean subtypes, string name, string signature, string ext
    |
      barrierGuardModel(package, type, subtypes, name, signature, ext, input, acceptingValue, kind,
        provenance, model) and
      e = interpretElement(package, type, subtypes, name, signature, ext)
    )
  }

  private newtype TInterpretNode =
    TElement_(Element n) or
    TNode_(Node n)

  /** An entity used to interpret a source/sink specification. */
  class InterpretNode extends TInterpretNode {
    /** Gets the element that this node corresponds to, if any. */
    SourceOrSinkElement asElement() { this = TElement_(result) }

    /** Gets the data-flow node that this node corresponds to, if any. */
    Node asNode() { this = TNode_(result) }

    /** Gets the call that this node corresponds to, if any. */
    DataFlowCall asCall() {
      this.asElement() = result.asCallInstruction().getUnconvertedResultExpression()
    }

    /** Gets the callable that this node corresponds to, if any. */
    DataFlowCallable asCallable() { result.getUnderlyingCallable() = this.asElement() }

    /** Gets the target of this call, if any. */
    Element getCallTarget() { result = this.asCall().getStaticCallTarget().getUnderlyingCallable() }

    /** Gets a textual representation of this node. */
    string toString() {
      result = this.asElement().toString()
      or
      result = this.asNode().toStringImpl()
      or
      result = this.asCall().toString()
    }

    /** Gets the location of this node. */
    Location getLocation() {
      result = this.asElement().getLocation()
      or
      result = this.asNode().getLocation()
      or
      result = this.asCall().getLocation()
    }
  }

  /** Provides additional sink specification logic. */
  bindingset[c]
  predicate interpretOutput(string c, InterpretNode mid, InterpretNode node) { none() }

  /** Provides additional source specification logic. */
  bindingset[c]
  predicate interpretInput(string c, InterpretNode mid, InterpretNode node) { none() }
}

module Private {
  import Impl::Private

  module Steps = Impl::Private::Steps<StepsInput>;

  module External {
    import Impl::Private::External
    import Impl::Private::External::SourceSinkInterpretation<SourceSinkInterpretationInput>
  }

  /**
   * Provides predicates for constructing summary components.
   */
  module SummaryComponent {
    private import Impl::Private::SummaryComponent as SC

    predicate parameter = SC::parameter/1;

    predicate argument = SC::argument/1;

    predicate content = SC::content/1;

    predicate withoutContent = SC::withoutContent/1;

    predicate withContent = SC::withContent/1;
  }

  /**
   * Provides predicates for constructing stacks of summary components.
   */
  module SummaryComponentStack {
    private import Impl::Private::SummaryComponentStack as SCS

    predicate singleton = SCS::singleton/1;

    predicate push = SCS::push/2;

    predicate argument = SCS::argument/1;
  }
}

module Public = Impl::Public;

private string getSourceToken(string output, int i) {
  sourceModel(_, _, _, _, _, _, output, _, _, _) and
  (
    i = 0 and
    not output.matches("%.%") and
    result = output
    or
    result = output.splitAt(".", i)
  )
}

private predicate interpretSourceRec(
  Element e, int i, string namespace, string type, boolean subtypes, string name, string signature,
  string ext, string output, string kind, string provenance, string model, boolean needsRef
) {
  sourceModel(namespace, type, subtypes, name, signature, ext, output, kind, provenance, model) and
  (
    i = 0 and
    e = interpretElement(namespace, type, subtypes, name, signature, ext) and
    needsRef = true
    or
    needsRef = false and
    exists(Element p, AccessPath::AccessPathTokenBase token, boolean needsRef0 |
      interpretSourceRec(p, i - 1, namespace, type, subtypes, name, signature, ext, output, kind,
        provenance, model, needsRef0) and
      token = getSourceToken(output, i - 1)
    |
      token.getName() = "ReturnValue" and
      e.(Call).getTarget() = p
      or
      exists(SourcePosition pos |
        token.getName() = "Parameter" and
        pos = decodePosition(token.getArgument(0)) and
        e = p.(Function).getParameter(pos.getArgumentIndex())
      )
      or
      exists(SourcePosition pos, Call c |
        token.getName() = "Argument" and
        pos = decodePosition(token.getArgument(0)) and
        (if needsRef0 = true then c.getTarget() = p else c = p)
      |
        e = c.getArgument(pos.getArgumentIndex())
        or
        pos.getArgumentIndex() = -1 and
        e = c.getQualifier()
      )
    )
  )
}

private predicate interpretSource(
  Element e, string namespace, string type, boolean subtypes, string name, string signature,
  string ext, string output, string kind, string provenance, string model
) {
  exists(boolean needsRef, Element e0 |
    interpretSourceRec(e0, count(int i | exists(getSourceToken(output, i))), namespace, type,
      subtypes, name, signature, ext, output, kind, provenance, model, needsRef)
  |
    if needsRef = true then e.(Call).getTarget() = e0 else e0 = e
  )
}

private class SourceModelCall extends Public::SourceElement {
  private string namespace;
  private string type;
  private boolean subtypes;
  private string name;
  private string signature;
  private string ext;

  SourceModelCall() {
    interpretSource(this, namespace, type, subtypes, name, signature, ext, _, _, _, _)
  }

  override predicate isSource(
    string output, string kind, Public::Provenance provenance, string model
  ) {
    sourceModel(namespace, type, subtypes, name, signature, ext, output, kind, provenance, model)
  }
}
