+int asn_strtoimax_lim(signed char *str, signed char **end, long long *intp)
{
  register int $307;
  register long long $29;
  register long long $308;
  register long long $309;
  register int $310;
  register signed char *$343;
  register signed char *$342;
  register signed char $341;
  register signed char *$340;
  register signed char $339;
  register signed char $338;
  $307 = 1;
  $308 = (~((unsigned long long) 0) >> 1) / 10;
  $309 = (~((unsigned long long) 0) >> 1) % 10;
  $343 = *$234;
  if ($305 >= $343) {
    return -2;
  }
  $341 = *$305;
  switch (*$305) {
    case 45:
      $309 = $309 + 1;
      $307 = -1;
    case 43:
      $305 = $305 + 1;
      $342 = *$234;
      if ($305 >= $342) {
        *$234 = $305;
        return -1;
      }
    
  }
  $29 = (long long) 0;
  for (; 1; $305 = $305 + 1) {
    $340 = *$234;
    if (! ($305 < $340)) {
      break;
    }
    $338 = *$305;
    switch (*$305) {
      case 48:
      case 49:
      case 50:
      case 51:
      case 52:
      case 53:
      case 54:
      case 55:
      case 56:
      case 57:
        $339 = *$305;
        $310 = $339 - 48;
        if ($29 < $308) {
          $29 = $29 * 10 + $310;
        } else {
          if ($29 == $308) {
            if ($310 <= $309) {
              if ($307 > 0) {
                $29 = $29 * 10 + $310;
              } else {
                $307 = 1;
                $29 = -$29 * 10 - $310;
              }
            } else {
              *$234 = $305;
              return -3;
            }
          } else {
            *$234 = $305;
            return -3;
          }
        }
        continue;
      default:
        *$234 = $305;
        *$306 = $307 * $29;
        return 1;
      
    }
  }
  *$234 = $305;
  *$306 = $307 * $29;
  return 0;
}
