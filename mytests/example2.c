features int[1,2] A;
features int[1,2] B;
features int[0,3] C;

int main() {
  	int x = [-10,10], y = [-10,10];
	int z = A*x+B*y+C;
	assert((z>=2*x+y) && (z<=2*x+y+2));
  return 0;
}