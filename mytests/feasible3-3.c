features int[0,31] A1;
features int[0,31] A2;
features int[0,31] A3;

int main() {
  int i=[0,32767];
  int i0 = i; 

  i=i+A1;
  i=i+A2;
  i=i+A3;
  assert(i>i0+A1); 
	
  return 0;
}