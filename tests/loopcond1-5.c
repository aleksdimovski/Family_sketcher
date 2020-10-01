features int[0,31] A;

int main() {
  int x=[-32767,32767];
  int y=0;
  while (x >= 0) {  
    x = x - 1;
	if (y<A) y=y+1; else y=y-1; 
  }
  assert (y<=1);
  return 0;
}