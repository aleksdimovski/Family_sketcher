features int[0,31] A;
features int[0,31] B;

int main() {
  int x=A;
  int y=0;
  while (x > B) {  
    x = x - 1;
	y = y + 1;
  }
  assert (y>2);
  return 0;
}