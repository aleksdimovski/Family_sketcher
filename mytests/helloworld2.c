features int[0,255] A;

int main() {
  	int x = [0,4294967295];
	int y=x*A;
	assert(y<=x+x);
  return 0;
}