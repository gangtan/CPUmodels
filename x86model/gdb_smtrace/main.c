#include <stdio.h>
#include <math.h>

float test(float a, float b) {
	float c = a / b;
	float d = c + c * 2.43414 - a * b;
	float e = c * d * d;
	double f = d - c + 3.1423423424 * 9999.0 * d * d * d * d * d + c * e - (d + e - c * a/b * b);
	double g = c - d * 2 + e + pow(2, 3);

	int i = (int)f;

	return c * d * e / f + g;
}

/*float test2(float a, float b) {
	double val = log2(a) + log2(b);
	double root = sqrt(sqrt(sqrt(val)));
	double s = pow(sin(root), 2) + pow(cos(root), 2);

	return s * val + sinh(root);
}
*/


int main() {
	int i = 0;
	float a = 1.2, b = 3.4;

	printf("product: %f\n", (a * b));

	printf("test: %f\n", test(a, b));
//	printf("test 2: %f\n", test2(a + b, a * b));
	printf ("float print test: %x\n", *(int*)&b);
 
	return 0;
}


/*
int iter(int n) {
	int i = 0;
	int res = 1;
	for(i = 1; i <= n; i++) {
		res *= i;	
	}
	return res;
}

int rec(int n) {
	if(n == 0) return 1;
	return n * rec(n-1);
}


int fin () {
	return -1;

} 

int main() {
	int res1 = rec(4);
	int res2 = iter(4);
	fin();
	return 0;
}
*/