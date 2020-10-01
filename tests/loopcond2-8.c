features int[0,255] F;
features int[0,255] A;

int main() {
  int x=[0,65535];
  int y=0;
  while (x >= A) {  
    x = x - 1;
	if (y<F) y=y+1; else y=y-1; 
  }
  assert (y>=1);
  return 0;
}