#include <stdio.h>

float test(float a, float b, int done) {
	float c = a / b;
	float d = c + c * 2.43414 - a * b;
	float e = c * d * d;
	double f = d - c + 3.1423423424 * 9999.0 * d * d * d * d * d + c * e - (d + e - c * a/b * b);

	int i = (int)f;

	return c * d * e;
}


int main() {
	int i = 0, done = 0;
	float a = 1.2, b = 3.4;

	printf("product: %f", (a * b));

	printf("test: %f", test(a, b, done));
	printf("test 2: %f", test(a + b, a * b, done));
 
	return 0;
}

/*
int main() {
	printf("hello world");
	return 0;
} */
