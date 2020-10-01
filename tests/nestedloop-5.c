features int[0,31] A;
features int[0,31] B;

int main() {
  int x=[0,65535];
  int s=0;
  int y=A;
  int x0=x, y0=y;
  while (x >= 0) {  
    x = x - 1;
	while (y>=B) {
		y=y-1;
		s=s+1;
	}
  }
  assert (s>=x0+y0);
  return 0;
}