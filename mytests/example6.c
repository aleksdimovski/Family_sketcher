features int[0,32767] A;

int main() {
  int x=[0,32767];
  int y=x;
  if ((x + 2) > A) 
	y = y + 1;
  else y = y -1; 
  assert (y>x);
  return 0;
}