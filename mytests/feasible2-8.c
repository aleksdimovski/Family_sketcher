features int[0,63] A1;
features int[0,63] A2;

int incr() { 
	return 3; 
}

int main() {
  int i=[0,32767];
  int i0 = i; 

  i=i+A1;
  i=i+A2;
  assert(i>i0+A1); 
	
  return 0;
}