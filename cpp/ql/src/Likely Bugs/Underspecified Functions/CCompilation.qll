/**
 * Provides C-compilation classification for the underspecified-function queries.
 */

import cpp

/**
 * Holds if `file` is compiled as C or is transitively included by a file compiled as C.
 */
predicate isFileCompiledAsC(File file) {
  file.compiledAsC()
  or
  exists(File including |
    isFileCompiledAsC(including) and
    including.getAnIncludedFile() = file
  )
}
