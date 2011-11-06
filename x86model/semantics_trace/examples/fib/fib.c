
// Calculates fibonacci numbers inefficiently.
//

#include <stdio.h>

int fib(int n) {
	if(n == 0) return 0;
	else if (n == 1) return 1;
	else return fib(n-1) + fib(n-2);	
}



void fin () { }

int main () {
	fib(4);
	fin();
	return 0;

}



