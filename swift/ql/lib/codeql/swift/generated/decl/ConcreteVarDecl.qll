// generated by codegen/codegen.py
import codeql.swift.elements.decl.VarDecl

class ConcreteVarDeclBase extends @concrete_var_decl, VarDecl {
  override string getAPrimaryQlClass() { result = "ConcreteVarDecl" }

  int getIntroducerInt() { concrete_var_decls(this, result) }
}
