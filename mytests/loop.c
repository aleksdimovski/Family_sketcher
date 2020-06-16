features int[0,31] A;

int main() {
  int x=10;
  int y=0;
  while (x > A) {  
    x = x - 1;
	y = y + 1;
  }
  assert (y<8);
  return 0;
}