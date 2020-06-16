features int[0,3] A;

int main() {
  	int x = [0,65535];
	int y=x*A;
	assert(y<=x+x);
  return 0;
}