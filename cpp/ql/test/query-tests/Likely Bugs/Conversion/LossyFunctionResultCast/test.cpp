
typedef long double MYLD;

bool getBool();
int getInt();
float getFloat();
double getDouble();
MYLD getMyLD();
float *getFloatPtr();
float &getFloatRef();
const float &getConstFloatRef();

void setPosInt(int x);
void setPosFloat(float x);

double round(double x);
float roundf(float x);

void test1()
{
	// simple

	if (getBool())
	{
		setPosInt(getBool());
		setPosFloat(getBool());
	}
	if (getInt())
	{
		setPosInt(getInt());
		setPosFloat(getInt());
	}
	if (getFloat()) // $ Alert // BAD
	{
		setPosInt(getFloat()); // $ Alert // BAD
		setPosFloat(getFloat());
	}
	if (getDouble()) // $ Alert // BAD
	{
		setPosInt(getDouble()); // $ Alert // BAD
		setPosFloat(getDouble());
	}
	if (getMyLD()) // $ Alert // BAD
	{
		setPosInt(getMyLD()); // $ Alert // BAD
		setPosFloat(getMyLD());
	}
	if (getFloatPtr())
	{
		// ...
	}
	if (getFloatRef()) // $ MISSING: Alert // BAD [NOT DETECTED]
	{
		setPosInt(getFloatRef()); // $ MISSING: Alert // BAD [NOT DETECTED]
		setPosFloat(getFloatRef());
	}
	if (getConstFloatRef()) // $ MISSING: Alert // BAD [NOT DETECTED]
	{
		setPosInt(getConstFloatRef()); // $ MISSING: Alert // BAD [NOT DETECTED]
		setPosFloat(getConstFloatRef());
	}

	// explicit cast

	if ((bool)getInt())
	{
		setPosInt(getInt());
		setPosFloat((float)getInt());
	}
	if ((bool)getFloat())
	{
		setPosInt((int)getFloat());
		setPosFloat(getFloat());
	}

	// explicit rounding

	if (roundf(getFloat()))
	{
		setPosInt(roundf(getFloat()));
		setPosFloat(roundf(getFloat()));
	}
	if (round(getDouble()))
	{
		setPosInt(round(getDouble()));
		setPosFloat(round(getDouble()));
	}
}

double pow(double x, double y);

int test2(double v, double w, int n)
{
	switch (n)
	{
	case 1:
		return pow(2, v); // GOOD
	case 2:
		return pow(10, v); // GOOD
	case 3:
		return pow(2.5, v); // $ Alert // BAD
	case 4:
		return pow(v, 2); // $ Alert // BAD
	case 5:
		return pow(v, w); // $ Alert // BAD
	};
}

double myRound1(double v)
{
	return round(v);
}

double myRound2(double v)
{
	double result = round(v);

	return result;
}

double myRound3(double v)
{
	return (v > 0) ? round(v) : 0;
}

void test3()
{
	int i = myRound1(1.5); // GOOD
	int j = myRound2(2.5); // GOOD
	int k = myRound3(3.5); // GOOD
}

double nestedRound(double v)
{
	return myRound2(v);
}

double recursiveRound(double v, int n)
{
	if (n <= 0)
		return round(v);
	return recursiveRound(v, n - 1);
}

double mutuallyRecursiveRound1(double v, int n);

double mutuallyRecursiveRound2(double v, int n)
{
	if (n <= 0)
		return round(v);
	return mutuallyRecursiveRound1(v, n - 1);
}

double mutuallyRecursiveRound1(double v, int n)
{
	return mutuallyRecursiveRound2(v, n);
}

double integerBasePower(double v)
{
	double result = pow(2, v);
	return result;
}

double sometimesRounded(double v)
{
	if (v > 0)
		return round(v);
	return getDouble();
}

void test4()
{
	int nested = nestedRound(1.5); // GOOD
	int recursive = recursiveRound(2.5, 3); // GOOD
	int mutual = mutuallyRecursiveRound1(3.5, 4); // GOOD
	int power = integerBasePower(5); // GOOD
	int mixed = sometimesRounded(-1.5); // GOOD
}
