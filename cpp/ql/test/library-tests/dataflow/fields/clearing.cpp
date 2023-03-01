struct S {
	int** x;
};

// We want a source of user input that can be both a pointer and a non-pointer. So we
// hack the testing a bit by providing an overload that takes a boolean to distinquish
// between the two while still satisfying the test requirement that the function must
// be named `user_input`.
int user_input();
int* user_input(bool);
void sink(...);

void test()
{
	{
		S s;
		**s.x = user_input();
		*s.x = nullptr;
		sink(**s.x); // clean
	}

	{
		S s;
		**s.x = user_input();
		**s.x = 0;
		sink(**s.x); // clean
	}

	{
		S s;
		*s.x = user_input(true);
		**s.x = 0;
		sink(*s.x); // $ ir
	}

	{
		S s;
		*s.x = user_input(true);
		s.x = nullptr;
		sink(*s.x); // clean
	}

	{
		S s;
		**s.x = user_input();
		s.x = nullptr;
		sink(*s.x); // clean
	}
}

void argument_source(int*);

struct S2
{
	int* val;
};

void test_uncertain_write_is_not_clear()
{
	S2 s;
	argument_source(s.val);
	s.val[10] = 0;
	sink(*s.val); // $ ir MISSING: ast
}