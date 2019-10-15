unsigned int factorial1 (unsigned int n) {
  unsigned int i = 0;
  unsigned int out = 1;
  while (i < n){
      i++;
      out = out*i ;
    } 
  return out ;
}
