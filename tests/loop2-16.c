features int[0,65535] A;
features int[0,65535] B;

int main() {
  int x=A;
  int y=0;
  while (x > B) {  
    x = x - 1;
	y = y + 1;
  }
  assert (y<8);
  return 0;
}