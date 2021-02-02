/**
 * Provides implementation classes modeling various standard formatting
 * functions (`printf`, `snprintf` etc).
 * See `semmle.code.cpp.models.interfaces.FormattingFunction` for usage
 * information.
 */

import semmle.code.cpp.models.interfaces.FormattingFunction
import semmle.code.cpp.models.interfaces.Alias
import semmle.code.cpp.models.interfaces.ArrayFunction
import semmle.code.cpp.models.interfaces.SideEffect

/**
 * The standard functions `printf`, `wprintf` and their glib variants.
 */
private class Printf extends FormattingFunction, AliasFunction, ArrayFunction, SideEffectFunction {
  Printf() {
    this instanceof TopLevelFunction and
    (
      hasGlobalOrStdName(["printf", "wprintf"]) or
      hasGlobalName(["printf_s", "wprintf_s", "g_printf"])
    ) and
    not exists(getDefinition().getFile().getRelativePath())
  }

  override int getFormatParameterIndex() { result = 0 }

  deprecated override predicate isWideCharDefault() {
    hasGlobalOrStdName("wprintf") or
    hasGlobalName("wprintf_s")
  }

  override predicate isOutputGlobal() { any() }

  override predicate parameterNeverEscapes(int n) { n = 0 }

  override predicate parameterEscapesOnlyViaReturn(int n) { none() }

  override predicate parameterIsAlwaysReturned(int n) { none() }

  override predicate hasArrayWithNullTerminator(int bufParam) {
    bufParam = this.getFormatParameterIndex()
  }

  override predicate hasArrayInput(int bufParam) { hasArrayWithNullTerminator(bufParam) }

  override predicate hasOnlySpecificReadSideEffects() { any() }

  override predicate hasOnlySpecificWriteSideEffects() { any() }

  override predicate hasSpecificReadSideEffect(ParameterIndex i, boolean buffer) {
    i = this.getFormatParameterIndex() and buffer = true
    or
    i >= this.getFirstFormatArgumentIndex() and buffer = true
  }
}

/**
 * The standard functions `fprintf`, `fwprintf` and their glib variants.
 */
private class Fprintf extends FormattingFunction, AliasFunction, ArrayFunction, SideEffectFunction {
  Fprintf() {
    this instanceof TopLevelFunction and
    (
      hasGlobalOrStdName(["fprintf", "fwprintf"]) or
      hasGlobalName("g_fprintf")
    ) and
    not exists(getDefinition().getFile().getRelativePath())
  }

  override int getFormatParameterIndex() { result = 1 }

  deprecated override predicate isWideCharDefault() { hasGlobalOrStdName("fwprintf") }

  override int getOutputParameterIndex(boolean isStream) { result = 0 and isStream = true }

  override predicate parameterNeverEscapes(int index) {
    index = [0 .. this.getACallToThisFunction().getNumberOfArguments()]
  }

  override predicate parameterEscapesOnlyViaReturn(int index) { none() }

  override predicate parameterIsAlwaysReturned(int index) { none() }

  override predicate hasArrayWithNullTerminator(int bufParam) {
    bufParam = this.getFormatParameterIndex()
  }

  override predicate hasArrayInput(int bufParam) { this.hasArrayWithNullTerminator(bufParam) }

  override predicate hasOnlySpecificReadSideEffects() { any() }

  override predicate hasOnlySpecificWriteSideEffects() { any() }

  override predicate hasSpecificWriteSideEffect(ParameterIndex i, boolean buffer, boolean mustWrite) {
    i = this.getOutputParameterIndex(true) and buffer = false and mustWrite = true
  }

  override predicate hasSpecificReadSideEffect(ParameterIndex i, boolean buffer) {
    i = this.getFormatParameterIndex() and buffer = true
    or
    i >= this.getFirstFormatArgumentIndex() and buffer = true
  }
}

/**
 * The standard function `sprintf` and its Microsoft and glib variants.
 */
private class Sprintf extends FormattingFunction, AliasFunction, ArrayFunction, SideEffectFunction {
  Sprintf() {
    this instanceof TopLevelFunction and
    (
      hasGlobalOrStdName([
          "sprintf", // sprintf(dst, format, args...)
          "wsprintf" // wsprintf(dst, format, args...)
        ])
      or
      hasGlobalName([
          "_sprintf_l", // _sprintf_l(dst, format, locale, args...)
          "__swprintf_l", // __swprintf_l(dst, format, locale, args...)
          "g_strdup_printf", // g_strdup_printf(format, ...)
          "g_sprintf", // g_sprintf(dst, format, ...)
          "__builtin___sprintf_chk" // __builtin___sprintf_chk(dst, flag, os, format, ...)
        ])
    ) and
    not exists(getDefinition().getFile().getRelativePath())
  }

  deprecated override predicate isWideCharDefault() {
    getParameter(getFormatParameterIndex())
        .getType()
        .getUnspecifiedType()
        .(PointerType)
        .getBaseType()
        .getSize() > 1
  }

  override int getFormatParameterIndex() {
    hasGlobalName("g_strdup_printf") and result = 0
    or
    hasGlobalName("__builtin___sprintf_chk") and result = 3
    or
    not getName() = ["g_strdup_printf", "__builtin___sprintf_chk"] and
    result = 1
  }

  override int getOutputParameterIndex(boolean isStream) {
    not hasGlobalName("g_strdup_printf") and result = 0 and isStream = false
  }

  override int getFirstFormatArgumentIndex() {
    if hasGlobalName("__builtin___sprintf_chk")
    then result = 4
    else result = getNumberOfParameters()
  }

  override predicate parameterNeverEscapes(int index) {
    index = [0 .. this.getACallToThisFunction().getNumberOfArguments()]
  }

  override predicate parameterEscapesOnlyViaReturn(int index) { none() }

  override predicate parameterIsAlwaysReturned(int index) { none() }

  override predicate hasArrayWithNullTerminator(int bufParam) {
    bufParam = [this.getOutputParameterIndex(false), this.getFormatParameterIndex()]
  }

  override predicate hasArrayInput(int bufParam) { bufParam = this.getFormatParameterIndex() }

  override predicate hasArrayOutput(int bufParam) { bufParam = this.getOutputParameterIndex(false) }

  override predicate hasOnlySpecificReadSideEffects() { any() }

  override predicate hasOnlySpecificWriteSideEffects() { any() }

  override predicate hasSpecificWriteSideEffect(ParameterIndex i, boolean buffer, boolean mustWrite) {
    i = getOutputParameterIndex(false) and buffer = true and mustWrite = true
  }

  override predicate hasSpecificReadSideEffect(ParameterIndex i, boolean buffer) {
    i = this.getFormatParameterIndex() and buffer = true
    or
    i >= this.getFirstFormatArgumentIndex() and buffer = true
  }
}

/**
 * Implements `Snprintf`.
 */
private class SnprintfImpl extends Snprintf, AliasFunction, ArrayFunction, SideEffectFunction {
  SnprintfImpl() {
    this instanceof TopLevelFunction and
    (
      hasGlobalOrStdName([
          "snprintf", // C99 defines snprintf
          "swprintf" // The s version of wide-char printf is also always the n version
        ])
      or
      // Microsoft has _snprintf as well as several other variations
      hasGlobalName([
          "sprintf_s", "snprintf_s", "swprintf_s", "_snprintf", "_snprintf_s", "_snprintf_l",
          "_snprintf_s_l", "_snwprintf", "_snwprintf_s", "_snwprintf_l", "_snwprintf_s_l",
          "_sprintf_s_l", "_swprintf_l", "_swprintf_s_l", "g_snprintf", "wnsprintf",
          "__builtin___snprintf_chk"
        ])
    ) and
    not exists(getDefinition().getFile().getRelativePath())
  }

  override int getFormatParameterIndex() {
    if getName().matches("%\\_l")
    then result = getFirstFormatArgumentIndex() - 2
    else result = getFirstFormatArgumentIndex() - 1
  }

  deprecated override predicate isWideCharDefault() {
    getParameter(getFormatParameterIndex())
        .getType()
        .getUnspecifiedType()
        .(PointerType)
        .getBaseType()
        .getSize() > 1
  }

  override int getOutputParameterIndex(boolean isStream) { result = 0 and isStream = false }

  override int getFirstFormatArgumentIndex() {
    exists(string name |
      name = getQualifiedName() and
      (
        name = "__builtin___snprintf_chk" and
        result = 5
        or
        name != "__builtin___snprintf_chk" and
        result = getNumberOfParameters()
      )
    )
  }

  override predicate returnsFullFormatLength() {
    (
      hasGlobalOrStdName("snprintf") or
      hasGlobalName(["g_snprintf", "__builtin___snprintf_chk", "snprintf_s"])
    ) and
    not exists(getDefinition().getFile().getRelativePath())
  }

  override int getSizeParameterIndex() { result = 1 }

  override predicate parameterNeverEscapes(int index) {
    index = [0 .. this.getACallToThisFunction().getNumberOfArguments()]
  }

  override predicate parameterEscapesOnlyViaReturn(int index) { none() }

  override predicate parameterIsAlwaysReturned(int index) { none() }

  override predicate hasArrayInput(int bufParam) { bufParam = getFormatParameterIndex() }

  override predicate hasArrayOutput(int bufParam) { bufParam = getOutputParameterIndex(false) }

  override predicate hasOnlySpecificReadSideEffects() { any() }

  override predicate hasOnlySpecificWriteSideEffects() { any() }

  override predicate hasSpecificWriteSideEffect(ParameterIndex i, boolean buffer, boolean mustWrite) {
    i = this.getOutputParameterIndex(false) and buffer = true and mustWrite = true
  }

  override predicate hasSpecificReadSideEffect(ParameterIndex i, boolean buffer) {
    i = this.getFormatParameterIndex() and buffer = true
    or
    i >= this.getFirstFormatArgumentIndex() and buffer = true
  }

  override ParameterIndex getParameterSizeIndex(ParameterIndex i) {
    i = this.getOutputParameterIndex(false) and result = this.getSizeParameterIndex()
  }
}

/**
 * The Microsoft `StringCchPrintf` function and variants.
 */
private class StringCchPrintf extends FormattingFunction, AliasFunction, ArrayFunction,
  SideEffectFunction {
  StringCchPrintf() {
    this instanceof TopLevelFunction and
    hasGlobalName([
        "StringCchPrintf", "StringCchPrintfEx", "StringCchPrintf_l", "StringCchPrintf_lEx",
        "StringCbPrintf", "StringCbPrintfEx", "StringCbPrintf_l", "StringCbPrintf_lEx"
      ]) and
    not exists(getDefinition().getFile().getRelativePath())
  }

  override int getFormatParameterIndex() {
    if getName().matches("%Ex") then result = 5 else result = 2
  }

  deprecated override predicate isWideCharDefault() {
    getParameter(getFormatParameterIndex())
        .getType()
        .getUnspecifiedType()
        .(PointerType)
        .getBaseType()
        .getSize() > 1
  }

  override int getOutputParameterIndex(boolean isStream) { result = 0 and isStream = false }

  override int getSizeParameterIndex() { result = 1 }

  override predicate parameterNeverEscapes(int index) {
    index = [0 .. this.getACallToThisFunction().getNumberOfArguments()]
  }

  override predicate parameterEscapesOnlyViaReturn(int index) { none() }

  override predicate parameterIsAlwaysReturned(int index) { none() }

  override predicate hasArrayInput(int bufParam) { bufParam = getFormatParameterIndex() }

  override predicate hasArrayOutput(int bufParam) { bufParam = getOutputParameterIndex(false) }

  override predicate hasOnlySpecificReadSideEffects() { any() }

  override predicate hasOnlySpecificWriteSideEffects() { any() }

  override predicate hasSpecificWriteSideEffect(ParameterIndex i, boolean buffer, boolean mustWrite) {
    i = this.getOutputParameterIndex(false) and buffer = true and mustWrite = false
  }

  override predicate hasSpecificReadSideEffect(ParameterIndex i, boolean buffer) {
    i = this.getFormatParameterIndex() and buffer = true
    or
    i >= this.getFirstFormatArgumentIndex() and buffer = true
  }

  override ParameterIndex getParameterSizeIndex(ParameterIndex i) {
    i = this.getOutputParameterIndex(false) and result = this.getSizeParameterIndex()
  }
}

/**
 * The standard function `syslog`.
 */
private class Syslog extends FormattingFunction, AliasFunction {
  Syslog() {
    this instanceof TopLevelFunction and
    hasGlobalName("syslog") and
    not exists(getDefinition().getFile().getRelativePath())
  }

  override int getFormatParameterIndex() { result = 1 }

  override predicate isOutputGlobal() { any() }

  override predicate parameterNeverEscapes(int index) {
    index = [0 .. this.getACallToThisFunction().getNumberOfArguments()]
  }

  override predicate parameterEscapesOnlyViaReturn(int index) { none() }

  override predicate parameterIsAlwaysReturned(int index) { none() }
}
