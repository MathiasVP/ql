#ifndef C_COMPILATION_LEAF_H
#define C_COMPILATION_LEAF_H

// The include graph has a cycle, even though include guards stop expansion.
#include "c-compilation-root.h"

int function_from_c_header();

void test_c_header_calls(int *p)
{
  function_from_c_header(); // $ Alert[cpp/too-few-arguments]
  function_from_c_header(p); // $ Alert[cpp/mistyped-function-arguments]
  function_from_c_header(1, 2); // $ Alert[cpp/futile-params]
  function_from_c_header(1); // Correct argument type and count.
  implicitly_declared_from_c_header(); // $ Alert[cpp/implicit-function-declaration]
}

int function_from_c_header(int x)
{
  return x;
}

#endif
