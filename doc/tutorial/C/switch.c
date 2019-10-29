int switch_test (int i) {
  
    switch(i) {
    case 0:
       return 0; 
    case 1:
      return 0;
    default : break;
    }
    return 0;
}

int switch_test_fail (int i) {
  
    switch(i) {
    case 0:
       return 0;
    case 1:
      return 0;
    }
    return 0;
}

int twice (int n) {
  switch (n) {
  case 0: return 0;
  case 1: n=2; return n;
  case -1: n= -2; return n;
  case 3: n=n+0; /* Fall Through */
  default: n=n+n; break;
  }
  return n;
}

int twice_fail (int n) {
  switch (n) {
  case 0: return 0;
  case 1: n=2; return n;
  case -1: n= -2; return n; 
  case 3: n=n+0; /* Fall Through */
  // default: n=n+n; break;
  }
  n = n + n;
  return n;
}
