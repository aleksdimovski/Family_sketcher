features int[0,7] A;
features int[0,7] C;

int main() {
  	int x = [-32768, 32767];
	int z = A*x+C;
	assert((z>=2*x) && (z<=2*x+2));
  return 0;
}