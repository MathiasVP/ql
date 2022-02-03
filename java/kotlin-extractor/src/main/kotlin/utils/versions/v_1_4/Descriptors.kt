package com.github.codeql.utils.versions

import com.github.codeql.KotlinUsesExtractor
import com.github.codeql.Severity
import org.jetbrains.kotlin.ir.ObsoleteDescriptorBasedAPI
import org.jetbrains.kotlin.ir.util.DeclarationStubGenerator
import org.jetbrains.kotlin.ir.util.SymbolTable

@OptIn(ObsoleteDescriptorBasedAPI::class)
fun <TIrStub> KotlinUsesExtractor.getIrStubFromDescriptor(generateStub: (DeclarationStubGenerator) -> TIrStub) : TIrStub? =
    (pluginContext.symbolTable as? SymbolTable) ?.let {
        val stubGenerator = DeclarationStubGenerator(pluginContext.moduleDescriptor, it, pluginContext.languageVersionSettings)
        generateStub(stubGenerator)
    } ?: run {
        logger.warn(Severity.ErrorHigh, "Plugin context has no symbol table, couldn't get IR stub")
        null
    }
