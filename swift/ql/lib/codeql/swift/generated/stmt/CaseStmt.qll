// generated by codegen/codegen.py
import codeql.swift.elements.stmt.CaseLabelItem
import codeql.swift.elements.stmt.Stmt
import codeql.swift.elements.decl.VarDecl

class CaseStmtBase extends @case_stmt, Stmt {
  override string getAPrimaryQlClass() { result = "CaseStmt" }

  Stmt getBody() {
    exists(Stmt x |
      case_stmts(this, x) and
      result = x.resolve()
    )
  }

  CaseLabelItem getLabel(int index) {
    exists(CaseLabelItem x |
      case_stmt_labels(this, index, x) and
      result = x.resolve()
    )
  }

  CaseLabelItem getALabel() { result = getLabel(_) }

  int getNumberOfLabels() { result = count(getALabel()) }

  VarDecl getVariable(int index) {
    exists(VarDecl x |
      case_stmt_variables(this, index, x) and
      result = x.resolve()
    )
  }

  VarDecl getAVariable() { result = getVariable(_) }

  int getNumberOfVariables() { result = count(getAVariable()) }
}
