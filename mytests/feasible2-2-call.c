features int[0,2] A1;
features int[0,2] A2;

int incr() { 
	return A1; 
}

int main() {
  int i=0;

  i=i+A1;
  i=i+A2;
  assert(i>incr()); 
	
  return 0;
}