// generated by codegen/codegen.py
private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.expr.Argument
import codeql.swift.elements.expr.LookupExpr

module Generated {
  class SubscriptExpr extends Synth::TSubscriptExpr, LookupExpr {
    override string getAPrimaryQlClass() { result = "SubscriptExpr" }

    Argument getImmediateArgument(int index) {
      result =
        Synth::convertArgumentFromRaw(Synth::convertSubscriptExprToRaw(this)
              .(Raw::SubscriptExpr)
              .getArgument(index))
    }

    final Argument getArgument(int index) { result = getImmediateArgument(index).resolve() }

    final Argument getAnArgument() { result = getArgument(_) }

    final int getNumberOfArguments() { result = count(getAnArgument()) }

    predicate hasDirectToStorageSemantics() {
      Synth::convertSubscriptExprToRaw(this).(Raw::SubscriptExpr).hasDirectToStorageSemantics()
    }

    predicate hasDirectToImplementationSemantics() {
      Synth::convertSubscriptExprToRaw(this)
          .(Raw::SubscriptExpr)
          .hasDirectToImplementationSemantics()
    }

    predicate hasOrdinarySemantics() {
      Synth::convertSubscriptExprToRaw(this).(Raw::SubscriptExpr).hasOrdinarySemantics()
    }
  }
}
