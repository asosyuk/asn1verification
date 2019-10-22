 int asn_strtoimax_lim(const char *str, const char **end, int *intp) {

    int sign = 1;

    if(str >= *end) return 0;

    switch(*str) {
    case '-':
        sign = -1;
        /* FALL THROUGH */
    case '+':
        str++;
        if(str >= *end) {
            *end = str;
            return 1;
        }
    }

    *end = str;
    *intp = sign;
    return 2;
}
