features int[-2,2] A;

int main() {
  int x=0;
  int y=0;
  if (x > A) 
	y = y + 1;
  else y = y -1; 
  assert (y>0);
  return 0;
}