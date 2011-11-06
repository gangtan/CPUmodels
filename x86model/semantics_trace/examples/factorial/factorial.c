

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
