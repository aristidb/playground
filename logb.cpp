//#include <iostream>
#include <math.h>

int f(double x) { return ilogb(x); }

#if 0
int main()
{
	std::cout << ilogb(1.0/0.0) << std::endl;
}
#endif
