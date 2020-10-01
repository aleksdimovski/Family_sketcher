features int[0,31] A;

int main() {
  int x=[0,65535];
  int y=x;
  if ((x + 5) > A) 
	y = y + 1;
  else y = y -1; 
  assert (y>x);
  return 0;
}