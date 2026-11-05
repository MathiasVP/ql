#define DEFINED

int x;

int fn1()
{
#ifdef DEFINED
	x++; // side-effect
#endif

	return 0;
}

int fn2()
{
#ifndef DEFINED
	x++; // hidden side-effect
#endif

	return 0;
}

int fn3()
{
#ifdef DEFINED
#else
	x++; // hidden side-effect
#endif

	return 0;
}

int fn4()
{
#ifdef DEFINED
#endif

	return 0;
}

/* in the following 4 cases, there is a possibility for code in the non-taken
 * branch - we can't check what that code is, because it isn't extracted, but
 * we assume there's a useful definition for the function in it */
#ifdef DEFINED
int fn5()
{
	return 0;
}
#else
#endif

#ifndef UNDEFINED
int fn6()
{
	return 0;
}
#else
#endif

#ifdef UNDEFINED
#else
int fn7()
{
	return 0;
}
#endif

#ifndef DEFINED
#else
int fn8()
{
	return 0;
}
#endif

// in this case, there is no alternate branch for code to go in
#ifdef DEFINED
int fn9()
{
	return 0;
}
#endif

void test()
{
	fn1();
	fn2();
	fn3();
	fn4(); // $ Alert // has no effect
	fn5();
	fn6();
	fn7();
	fn8();
	fn9(); // $ Alert // has no effect
}

// Each preprocessor exclusion must also suppress calls through multiple callers.
int disabled_code_caller()
{
	return fn2();
}

int disabled_code_transitive_caller()
{
	return disabled_code_caller();
}

int conditional_definition_caller()
{
	return fn5();
}

int conditional_definition_transitive_caller()
{
	return conditional_definition_caller();
}

// A caller can reach both kinds of excluded function.
int both_exclusions(int condition)
{
	return condition ? disabled_code_transitive_caller() : conditional_definition_transitive_caller();
}

// A taken preprocessor branch without an alternative must not suppress a call.
int pure_transitive_caller()
{
	return fn4();
}

int conditional_cycle_b(int n);

int conditional_cycle_a(int n)
{
	return n ? conditional_cycle_b(n - 1) : fn2();
}

int conditional_cycle_b(int n)
{
	return conditional_cycle_a(n);
}

void test_transitive_preprocessor_exclusions(int n)
{
	disabled_code_transitive_caller();
	conditional_definition_transitive_caller();
	both_exclusions(n);
	conditional_cycle_b(n);
	pure_transitive_caller(); // $ Alert[cpp/useless-expression]
}
