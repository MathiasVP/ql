class SharedDestructorReachability
{
public:
	SharedDestructorReachability()
	{
		first = new int; // GOOD
		second = new int; // GOOD
		third = new int; // GOOD
		missing = new int; // $ Alert // BAD: not released
	}

	~SharedDestructorReachability()
	{
		cleanup();
	}

	void cleanup()
	{
		cleanupFirst();
		cleanupRemaining(false);
	}

	void cleanupFirst()
	{
		delete first;
	}

	void cleanupRemaining(bool recurse)
	{
		delete second;
		delete third;
		if (recurse)
			cleanup();
	}

private:
	int *first;
	int *second;
	int *third;
	int *missing;
};

class UnrelatedDestructorReachability
{
public:
	UnrelatedDestructorReachability()
	{
		first = new int; // $ Alert // BAD: not released
	}

	~UnrelatedDestructorReachability()
	{
		cleanup();
	}

	void cleanup()
	{
	}

private:
	int *first;
};
