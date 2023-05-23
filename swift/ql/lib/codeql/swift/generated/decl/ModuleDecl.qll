// generated by codegen/codegen.py
private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.decl.TypeDecl

module Generated {
  class ModuleDecl extends Synth::TModuleDecl, TypeDecl {
    override string getAPrimaryQlClass() { result = "ModuleDecl" }

    /**
     * Holds if this module is the built-in one.
     */
    predicate isBuiltinModule() {
      Synth::convertModuleDeclToRaw(this).(Raw::ModuleDecl).isBuiltinModule()
    }

    /**
     * Holds if this module is a system one.
     */
    predicate isSystemModule() {
      Synth::convertModuleDeclToRaw(this).(Raw::ModuleDecl).isSystemModule()
    }

    /**
     * Gets the `index`th imported module of this module declaration (0-based).
     *Gets any of the imported modules of this module declaration.
     *
     * This includes nodes from the "hidden" AST. It can be overridden in subclasses to change the
     * behavior of both the `Immediate` and non-`Immediate` versions.
     */
    ModuleDecl getAnImmediateImportedModule() {
      result =
        Synth::convertModuleDeclFromRaw(Synth::convertModuleDeclToRaw(this)
              .(Raw::ModuleDecl)
              .getAnImportedModule())
    }

    /**
     * Gets the `index`th imported module of this module declaration (0-based).
     *Gets any of the imported modules of this module declaration.
     */
    final ModuleDecl getAnImportedModule() {
      exists(ModuleDecl immediate |
        immediate = this.getAnImmediateImportedModule() and
        if exists(this.getResolveStep()) then result = immediate else result = immediate.resolve()
      )
    }

    /**
     * Gets the number of imported modules of this module declaration.
     */
    final int getNumberOfImportedModules() { result = count(this.getAnImportedModule()) }

    /**
     * Gets the `index`th exported module of this module declaration (0-based).
     *Gets any of the exported modules of this module declaration.
     *
     * This includes nodes from the "hidden" AST. It can be overridden in subclasses to change the
     * behavior of both the `Immediate` and non-`Immediate` versions.
     */
    ModuleDecl getAnImmediateExportedModule() {
      result =
        Synth::convertModuleDeclFromRaw(Synth::convertModuleDeclToRaw(this)
              .(Raw::ModuleDecl)
              .getAnExportedModule())
    }

    /**
     * Gets the `index`th exported module of this module declaration (0-based).
     *Gets any of the exported modules of this module declaration.
     */
    final ModuleDecl getAnExportedModule() {
      exists(ModuleDecl immediate |
        immediate = this.getAnImmediateExportedModule() and
        if exists(this.getResolveStep()) then result = immediate else result = immediate.resolve()
      )
    }

    /**
     * Gets the number of exported modules of this module declaration.
     */
    final int getNumberOfExportedModules() { result = count(this.getAnExportedModule()) }
  }
}
