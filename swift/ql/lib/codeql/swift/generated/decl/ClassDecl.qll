// generated by codegen/codegen.py
import codeql.swift.elements.decl.NominalTypeDecl

class ClassDeclBase extends @class_decl, NominalTypeDecl {
  override string getAPrimaryQlClass() { result = "ClassDecl" }
}
