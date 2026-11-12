import cpp
import utils.test.InlineExpectationsTest
import semmle.code.cpp.dataflow.new.DataFlow::DataFlow

bindingset[s]
string quote(string s) { if s.matches("% %") then result = "\"" + s + "\"" else result = s }

string formatNumberOfNodesForExpr(Expr e) {
  exists(int n | n = strictcount(Node node | node.asExpr() = e) | n > 1 and result = ": " + n)
}

string formatNumberOfNodesForParameter(Parameter p) {
  exists(int n | n = strictcount(Node node | node.asParameter() = p) | n > 1 and result = ": " + n)
}

Node referenceNode(Expr e, int index) {
  index = 0 and result.asExpr() = e
  or
  index > 0 and result.asIndirectExpr(index) = e
}

module AsExprTest implements TestSig {
  string getARelevantTag() {
    result = ["asExpr", "numberOfNodes", "asParameter", "parameterNode", "referenceMapping"]
  }

  predicate hasActualResult(Location location, string element, string tag, string value) {
    exists(Node n, Expr e, string exprString |
      e = n.asExpr() and
      location = e.getLocation() and
      element = n.toString() and
      exprString = e.toString()
    |
      tag = "asExpr" and
      // If the `toString` on the node is identical to the `toString` of the
      // expression then we don't show it in the expected output.
      if exprString = element
      then value = quote(exprString)
      else value = quote(exprString + "(" + element + ")")
      or
      tag = "numberOfNodes" and
      value = quote(exprString + formatNumberOfNodesForExpr(e))
    )
    or
    exists(Node n, Parameter p, string paramString |
      not p.getName().matches("(unnamed%") and
      location = p.getLocation() and
      element = n.toString() and
      paramString = p.toString()
    |
      p = n.asParameter() and
      (
        tag = "asParameter" and
        // If the `toString` on the node is identical to the `toString` of the
        // parameter then we don't show it in the expected output.
        if paramString = element
        then value = quote(paramString)
        else value = quote(paramString + "(" + element + ")")
        or
        tag = "numberOfNodes" and
        value = quote(paramString + formatNumberOfNodesForParameter(p))
      )
      or
      parameterNode(p) = n and
      tag = "parameterNode" and
      // If the `toString` on the node is identical to the `toString` of the
      // parameter then we don't show it in the expected output.
      if paramString = element
      then value = quote(paramString)
      else value = quote(paramString + "(" + element + ")")
    )
    or
    exists(Expr e, int index, Node n |
      e.getEnclosingFunction().hasName("test_reference_values") and
      not e instanceof Conversion and
      e.getUnspecifiedType() instanceof ReferenceType and
      n = referenceNode(e, index) and
      location = e.getLocation() and
      element = e.toString() and
      tag = "referenceMapping" and
      value =
        quote(e.toString() + ":" + index + ":" + n.getType() + ":" + count(referenceNode(e, index)))
    )
  }
}

import MakeTest<AsExprTest>
