unsigned int pow2(unsigned int n) {
  unsigned int res = 1;
  while(n) {
    res = res + res;
    n = n - 1;
  }
  return res;
}
