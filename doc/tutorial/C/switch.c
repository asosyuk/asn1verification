int switch_test(int i) {
  
    switch(i) {
    case 0:
       return 0 ; break;
    case 1:
      return 1 ; break;
    default : return 2;
    }
}

int twice (int n) {
  switch (n) {
  case 0: return 0;
  case 1: n=2; return n;
  case -1: n= -2; return n;
  // case 3: n=n+0;
  // default: n=n+n; break;
  }
  return n + n;
}

int f(unsigned int x) { switch (x) {
   case 1: return 2; break;
   case 2: case 3: case 0xffffffff: return 1; break;
   default: return 1; }
}
