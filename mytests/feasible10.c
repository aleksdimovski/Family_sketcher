features int[0,31] A1;
features int[0,31] A2;
features int[0,31] A3;
features int[0,31] A4;
features int[0,31] A5;
features int[0,31] A6;
features int[0,31] A7;
features int[0,31] A8;
features int[0,31] A9;
features int[0,31] A10;

int main() {
  int i=[0,32767];
  int i0 = i; 

  i=i+A1;
  i=i+A2;
  i=i+A3;
  i=i+A4;
  i=i+A5;
  i=i+A6;
  i=i+A7;
  i=i+A8;
  i=i+A9;	
  i=i+A10;
  assert(i>i0+A1); 
	
  return 0;
}