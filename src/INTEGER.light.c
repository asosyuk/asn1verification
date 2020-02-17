struct asn_codec_ctx_s;
struct asn_enc_rval_s;
struct asn_dec_rval_s;
struct asn_bit_data_s;
struct asn_bit_outp_s;
struct asn_per_constraint_s;
struct asn_per_constraints_s;
struct asn_random_fill_result_s;
struct asn_oer_constraint_number_s;
struct asn_oer_constraints_s;
struct asn_type_selector_result_s;
struct asn_TYPE_operation_s;
struct asn_encoding_constraints_s;
struct asn_TYPE_descriptor_s;
struct asn_TYPE_member_s;
struct ASN__PRIMITIVE_TYPE_s;
struct asn_INTEGER_enum_map_s;
struct asn_INTEGER_specifics_s;
union _2079;
struct e2v_key;
struct asn_codec_ctx_s {
  unsigned int max_stack_size;
};

struct asn_enc_rval_s {
  int encoded;
  struct asn_TYPE_descriptor_s *failed_type;
  void *structure_ptr;
};

struct asn_dec_rval_s {
  int code;
  unsigned int consumed;
};

struct asn_bit_data_s {
  unsigned char *buffer;
  unsigned int nboff;
  unsigned int nbits;
  unsigned int moved;
  int (*refill)(struct asn_bit_data_s *);
  void *refill_key;
};

struct asn_bit_outp_s {
  unsigned char *buffer;
  unsigned int nboff;
  unsigned int nbits;
  unsigned char tmpspace[32];
  int (*output)(void *, unsigned int, void *);
  void *op_key;
  unsigned int flushed_bytes;
};

struct asn_per_constraint_s {
  int flags;
  int range_bits;
  int effective_bits;
  int lower_bound;
  int upper_bound;
};

struct asn_per_constraints_s {
  struct asn_per_constraint_s value;
  struct asn_per_constraint_s size;
  int (*value2code)(unsigned int);
  int (*code2value)(unsigned int);
};

struct asn_random_fill_result_s {
  int code;
  unsigned int length;
};

struct asn_oer_constraint_number_s {
  unsigned int width;
  unsigned int positive;
};

struct asn_oer_constraints_s {
  struct asn_oer_constraint_number_s value;
  int size;
};

struct asn_type_selector_result_s {
  struct asn_TYPE_descriptor_s *type_descriptor;
  unsigned int presence_index;
};

struct asn_TYPE_operation_s {
  void (*free_struct)(struct asn_TYPE_descriptor_s *, void *, int);
  int (*print_struct)(struct asn_TYPE_descriptor_s *, void *, int, int (*)(void *, unsigned int, void *), void *);
  int (*compare_struct)(struct asn_TYPE_descriptor_s *, void *, void *);
  void (*ber_decoder)(struct asn_dec_rval_s *, struct asn_codec_ctx_s *, struct asn_TYPE_descriptor_s *, void **, void *, unsigned int, int);
  void (*der_encoder)(struct asn_enc_rval_s *, struct asn_TYPE_descriptor_s *, void *, int, unsigned int, int (*)(void *, unsigned int, void *), void *);
  void (*xer_decoder)(struct asn_dec_rval_s *, struct asn_codec_ctx_s *, struct asn_TYPE_descriptor_s *, void **, signed char *, void *, unsigned int);
  void (*xer_encoder)(struct asn_enc_rval_s *, struct asn_TYPE_descriptor_s *, void *, int, int, int (*)(void *, unsigned int, void *), void *);
  void (*oer_decoder)(struct asn_dec_rval_s *, struct asn_codec_ctx_s *, struct asn_TYPE_descriptor_s *, struct asn_oer_constraints_s *, void **, void *, unsigned int);
  void (*oer_encoder)(struct asn_enc_rval_s *, struct asn_TYPE_descriptor_s *, struct asn_oer_constraints_s *, void *, int (*)(void *, unsigned int, void *), void *);
  void (*uper_decoder)(struct asn_dec_rval_s *, struct asn_codec_ctx_s *, struct asn_TYPE_descriptor_s *, struct asn_per_constraints_s *, void **, struct asn_bit_data_s *);
  void (*uper_encoder)(struct asn_enc_rval_s *, struct asn_TYPE_descriptor_s *, struct asn_per_constraints_s *, void *, struct asn_bit_outp_s *);
  void (*random_fill)(struct asn_random_fill_result_s *, struct asn_TYPE_descriptor_s *, void **, struct asn_encoding_constraints_s *, unsigned int);
  unsigned int (*outmost_tag)(struct asn_TYPE_descriptor_s *, void *, int, unsigned int);
};

struct asn_encoding_constraints_s {
  struct asn_oer_constraints_s *oer_constraints;
  struct asn_per_constraints_s *per_constraints;
  int (*general_constraints)(struct asn_TYPE_descriptor_s *, void *, void (*)(void *, struct asn_TYPE_descriptor_s *, void *, signed char *, ...), void *);
};

struct asn_TYPE_descriptor_s {
  signed char *name;
  signed char *xml_tag;
  struct asn_TYPE_operation_s *op;
  unsigned int *tags;
  unsigned int tags_count;
  unsigned int *all_tags;
  unsigned int all_tags_count;
  struct asn_encoding_constraints_s encoding_constraints;
  struct asn_TYPE_member_s *elements;
  unsigned int elements_count;
  void *specifics;
};

struct asn_TYPE_member_s {
  int flags;
  unsigned int optional;
  unsigned int memb_offset;
  unsigned int tag;
  int tag_mode;
  struct asn_TYPE_descriptor_s *type;
  void (*type_selector)(struct asn_type_selector_result_s *, struct asn_TYPE_descriptor_s *, void *);
  struct asn_encoding_constraints_s encoding_constraints;
  int (*default_value_cmp)(void *);
  int (*default_value_set)(void **);
  signed char *name;
};

struct ASN__PRIMITIVE_TYPE_s {
  unsigned char *buf;
  unsigned int size;
};

struct asn_INTEGER_enum_map_s {
  int nat_value;
  unsigned int enum_len;
  signed char *enum_name;
};

struct asn_INTEGER_specifics_s {
  struct asn_INTEGER_enum_map_s *value2enum;
  unsigned int *enum2value;
  int map_count;
  int extension;
  int strict_enumeration;
  int field_width;
  int field_unsigned;
};

union _2079 {
  unsigned char *c_buf;
  unsigned char *nc_buf;
};

struct e2v_key {
  signed char *start;
  signed char *stop;
  struct asn_INTEGER_enum_map_s *vemap;
  unsigned int *evmap;
};

extern unsigned int __compcert_va_int32(void *);
extern unsigned long long __compcert_va_int64(void *);
extern double __compcert_va_float64(void *);
extern void *__compcert_va_composite(void *, unsigned int);
extern long long __compcert_i64_dtos(double);
extern unsigned long long __compcert_i64_dtou(double);
extern double __compcert_i64_stod(long long);
extern double __compcert_i64_utod(unsigned long long);
extern float __compcert_i64_stof(long long);
extern float __compcert_i64_utof(unsigned long long);
extern long long __compcert_i64_sdiv(long long, long long);
extern unsigned long long __compcert_i64_udiv(unsigned long long, unsigned long long);
extern long long __compcert_i64_smod(long long, long long);
extern unsigned long long __compcert_i64_umod(unsigned long long, unsigned long long);
extern long long __compcert_i64_shl(long long, int);
extern unsigned long long __compcert_i64_shr(unsigned long long, int);
extern long long __compcert_i64_sar(long long, int);
extern long long __compcert_i64_smulh(long long, long long);
extern unsigned long long __compcert_i64_umulh(unsigned long long, unsigned long long);
extern void __builtin_debug(int, ...);
extern void *malloc(unsigned int);
extern void *calloc(unsigned int, unsigned int);
extern void *realloc(void *, unsigned int);
extern void free(void *);
extern void *bsearch(void *, void *, unsigned int, unsigned int, int (*)(void *, void *));
extern int memcmp(void *, void *, unsigned int);
extern int asn_get_few_bits(struct asn_bit_data_s *, int);
extern int asn_get_many_bits(struct asn_bit_data_s *, unsigned char *, int, int);
extern int asn_put_few_bits(struct asn_bit_outp_s *, unsigned int, int);
extern int asn_put_many_bits(struct asn_bit_outp_s *, unsigned char *, int);
extern int uper_get_length(struct asn_bit_data_s *, int, unsigned int, int *);
extern int uper_get_constrained_whole_number(struct asn_bit_data_s *, unsigned int *, int);
extern int per_long_range_rebase(int, int, int, unsigned int *);
extern int per_long_range_unrebase(unsigned int, int, int, int *);
extern int uper_put_constrained_whole_number_u(struct asn_bit_outp_s *, unsigned int, int);
extern int uper_put_length(struct asn_bit_outp_s *, unsigned int, int *);
extern int asn_generic_no_constraint(struct asn_TYPE_descriptor_s *, void *, void (*)(void *, struct asn_TYPE_descriptor_s *, void *, signed char *, ...), void *);
extern int asn_generic_unknown_constraint(struct asn_TYPE_descriptor_s *, void *, void (*)(void *, struct asn_TYPE_descriptor_s *, void *, signed char *, ...), void *);
extern long long asn_random_between(long long, long long);
extern void oer_decode_primitive(struct asn_dec_rval_s *, struct asn_codec_ctx_s *, struct asn_TYPE_descriptor_s *, struct asn_oer_constraints_s *, void **, void *, unsigned int);
extern void oer_encode_primitive(struct asn_enc_rval_s *, struct asn_TYPE_descriptor_s *, struct asn_oer_constraints_s *, void *, int (*)(void *, unsigned int, void *), void *);
extern unsigned int asn_TYPE_outmost_tag(struct asn_TYPE_descriptor_s *, void *, int, unsigned int);
extern void __assert_fail(signed char *, signed char *, unsigned int, signed char *);
extern int asn__format_to_callback(int (*)(void *, unsigned int, void *), void *, signed char *, ...);
extern void ASN__PRIMITIVE_TYPE_free(struct asn_TYPE_descriptor_s *, void *, int);
extern void ber_decode_primitive(struct asn_dec_rval_s *, struct asn_codec_ctx_s *, struct asn_TYPE_descriptor_s *, void **, void *, unsigned int, int);
extern void der_encode_primitive(struct asn_enc_rval_s *, struct asn_TYPE_descriptor_s *, void *, int, unsigned int, int (*)(void *, unsigned int, void *), void *);
extern void xer_decode_primitive(struct asn_dec_rval_s *, struct asn_codec_ctx_s *, struct asn_TYPE_descriptor_s *, void **, unsigned int, signed char *, void *, unsigned int, int (*)(struct asn_TYPE_descriptor_s *, void *, void *, unsigned int));
extern void INTEGER_decode_oer(struct asn_dec_rval_s *, struct asn_codec_ctx_s *, struct asn_TYPE_descriptor_s *, struct asn_oer_constraints_s *, void **, void *, unsigned int);
extern void INTEGER_encode_oer(struct asn_enc_rval_s *, struct asn_TYPE_descriptor_s *, struct asn_oer_constraints_s *, void *, int (*)(void *, unsigned int, void *), void *);
extern int *__errno_location(void);
void INTEGER_encode_der(struct asn_enc_rval_s *, struct asn_TYPE_descriptor_s *, void *, int, unsigned int, int (*)(void *, unsigned int, void *), void *);
int INTEGER__dump(struct asn_TYPE_descriptor_s *, struct ASN__PRIMITIVE_TYPE_s *, int (*)(void *, unsigned int, void *), void *, int);
int INTEGER_print(struct asn_TYPE_descriptor_s *, void *, int, int (*)(void *, unsigned int, void *), void *);
int INTEGER__compar_enum2value(void *, void *);
struct asn_INTEGER_enum_map_s *INTEGER_map_enum2value(struct asn_INTEGER_specifics_s *, signed char *, signed char *);
int INTEGER__compar_value2enum(void *, void *);
struct asn_INTEGER_enum_map_s *INTEGER_map_value2enum(struct asn_INTEGER_specifics_s *, int);
int INTEGER_st_prealloc(struct ASN__PRIMITIVE_TYPE_s *, int);
int INTEGER__xer_body_decode(struct asn_TYPE_descriptor_s *, void *, void *, unsigned int);
void INTEGER_decode_xer(struct asn_dec_rval_s *, struct asn_codec_ctx_s *, struct asn_TYPE_descriptor_s *, void **, signed char *, void *, unsigned int);
void INTEGER_encode_xer(struct asn_enc_rval_s *, struct asn_TYPE_descriptor_s *, void *, int, int, int (*)(void *, unsigned int, void *), void *);
void INTEGER_decode_uper(struct asn_dec_rval_s *, struct asn_codec_ctx_s *, struct asn_TYPE_descriptor_s *, struct asn_per_constraints_s *, void **, struct asn_bit_data_s *);
void INTEGER_encode_uper(struct asn_enc_rval_s *, struct asn_TYPE_descriptor_s *, struct asn_per_constraints_s *, void *, struct asn_bit_outp_s *);
long long asn__integer_convert(unsigned char *, unsigned char *);
int asn_INTEGER2imax(struct ASN__PRIMITIVE_TYPE_s *, long long *);
int asn_INTEGER2umax(struct ASN__PRIMITIVE_TYPE_s *, unsigned long long *);
int asn_umax2INTEGER(struct ASN__PRIMITIVE_TYPE_s *, unsigned long long);
int asn_imax2INTEGER(struct ASN__PRIMITIVE_TYPE_s *, long long);
int asn_INTEGER2long(struct ASN__PRIMITIVE_TYPE_s *, int *);
int asn_INTEGER2ulong(struct ASN__PRIMITIVE_TYPE_s *, unsigned int *);
int asn_long2INTEGER(struct ASN__PRIMITIVE_TYPE_s *, int);
int asn_ulong2INTEGER(struct ASN__PRIMITIVE_TYPE_s *, unsigned int);
int asn_strtoimax_lim(signed char *, signed char **, long long *);
int asn_strtoumax_lim(signed char *, signed char **, unsigned long long *);
int asn_strtol_lim(signed char *, signed char **, int *);
int asn_strtoul_lim(signed char *, signed char **, unsigned int *);
int INTEGER_compare(struct asn_TYPE_descriptor_s *, void *, void *);
void INTEGER_random_fill(struct asn_random_fill_result_s *, struct asn_TYPE_descriptor_s *, void **, struct asn_encoding_constraints_s *, unsigned int);
signed char const __stringlit_10[12] = "Unreachable";

signed char const __stringlit_6[17] = "0123456789ABCDEF";

signed char const __stringlit_11[18] = "variants[18] == 0";

signed char const __stringlit_1[8] = "INTEGER";

signed char const __stringlit_4[6] = "<%s/>";

signed char const __stringlit_2[5] = "%lld";

signed char const __stringlit_3[5] = "%llu";

signed char const __stringlit_5[10] = "%lld (%s)";

signed char const __stringlit_7[9] = "<absent>";

signed char const __stringlit_8[32] = "../../asn1c/skeletons/INTEGER.c";

signed char const __stringlit_12[13] = "emap_len > 0";

signed char const __stringlit_9[15] = "!\042Unreachable\042";

unsigned int const asn_DEF_INTEGER_tags[1] = { 8, };

struct asn_TYPE_operation_s asn_OP_INTEGER = { &ASN__PRIMITIVE_TYPE_free,
  &INTEGER_print, &INTEGER_compare, &ber_decode_primitive,
  &INTEGER_encode_der, &INTEGER_decode_xer, &INTEGER_encode_xer,
  &INTEGER_decode_oer, &INTEGER_encode_oer, &INTEGER_decode_uper,
  &INTEGER_encode_uper, &INTEGER_random_fill, 0, };

struct asn_TYPE_descriptor_s asn_DEF_INTEGER = { &__stringlit_1,
  &__stringlit_1, &asn_OP_INTEGER, &asn_DEF_INTEGER_tags, 1,
  &asn_DEF_INTEGER_tags, 1, 0, 0, &asn_generic_no_constraint, 0, 0, 0, };

void INTEGER_encode_der(struct asn_enc_rval_s *$_res, struct asn_TYPE_descriptor_s *$td, void *$sptr, int $tag_mode, unsigned int $tag, int (*$cb)(void *, unsigned int, void *), void *$app_key)
{
  struct asn_enc_rval_s rval;
  struct ASN__PRIMITIVE_TYPE_s effective_integer;
  union _2079 unconst;
  struct asn_enc_rval_s _res__1;
  register struct ASN__PRIMITIVE_TYPE_s *$st;
  register unsigned char *$buf;
  register unsigned char *$end1;
  register int $shift;
  register unsigned int $349;
  register unsigned char $348;
  register unsigned char $347;
  register unsigned char $346;
  register unsigned char *$345;
  register unsigned char *$344;
  register unsigned char *$343;
  register unsigned int $342;
  register unsigned char *$341;
  register void *$340;
  $st = (struct ASN__PRIMITIVE_TYPE_s *) $sptr;
  for (; 1; ({ break; })) {
    /*skip*/;
  }
  $341 = (*$st).buf;
  if ($341) {
    $buf = (*$st).buf;
    $349 = (*$st).size;
    $end1 = $buf + $349 - 1;
    for (; 1; $buf = $buf + 1) {
      if (! ($buf < $end1)) {
        break;
      }
      $346 = *$buf;
      switch ($346) {
        case 0:
          $348 = *($buf + 1);
          if (($348 & 128) == 0) {
            continue;
          }
          break;
        case 255:
          $347 = *($buf + 1);
          if ($347 & 128) {
            continue;
          }
          break;
        
      }
      break;
    }
    $345 = (*$st).buf;
    $shift = $buf - $345;
    if ($shift) {
      $344 = (*$st).buf;
      unconst.c_buf = $344;
      $343 = unconst.nc_buf;
      effective_integer.buf = $343 + $shift;
      $342 = (*$st).size;
      effective_integer.size = $342 - $shift;
      $st = &effective_integer;
    }
  }
  der_encode_primitive(&_res__1, $td, $st, $tag_mode, $tag, $cb, $app_key);
  rval = _res__1;
  $340 = rval.structure_ptr;
  if ($340 == &effective_integer) {
    rval.structure_ptr = $sptr;
  }
  *$_res = rval;
  return;
}

int INTEGER__dump(struct asn_TYPE_descriptor_s *$td, struct ASN__PRIMITIVE_TYPE_s *$st, int (*$cb)(void *, unsigned int, void *), void *$app_key, int $plainOrXER)
{
  signed char scratch[32];
  long long value;
  register struct asn_INTEGER_specifics_s *$specs;
  register unsigned char *$buf;
  register unsigned char *$buf_end;
  register int $wrote;
  register signed char *$p;
  register int $ret;
  register struct asn_INTEGER_enum_map_s *$el;
  register signed char *$h2c;
  register int $363;
  register int $362;
  register signed char *$361;
  register signed char *$360;
  register signed char *$359;
  register int $358;
  register int $357;
  register int $356;
  register int *$355;
  register int $354;
  register int $353;
  register int $352;
  register signed char *$351;
  register int $350;
  register int *$349;
  register int $348;
  register int $347;
  register struct asn_INTEGER_enum_map_s *$346;
  register void *$345;
  register int $344;
  register int $343;
  register int $342;
  register int $341;
  register int $340;
  register void *$381;
  register unsigned int $380;
  register unsigned char *$379;
  register int $378;
  register long long $377;
  register int $376;
  register long long $375;
  register signed char *$374;
  register long long $373;
  register signed char *$372;
  register int $371;
  register int $370;
  register long long $369;
  register int $368;
  register signed char $367;
  register unsigned char $366;
  register signed char $365;
  register unsigned char $364;
  $381 = (*$td).specifics;
  $specs = (struct asn_INTEGER_specifics_s *) $381;
  $buf = (*$st).buf;
  $379 = (*$st).buf;
  $380 = (*$st).size;
  $buf_end = $379 + $380;
  $wrote = 0;
  if ($specs) {
    $378 = (*$specs).field_unsigned;
    $342 = (_Bool) $378;
  } else {
    $342 = 0;
  }
  if ($342) {
    $340 = asn_INTEGER2umax($st, (unsigned long long *) &value);
    $ret = $340;
  } else {
    $341 = asn_INTEGER2imax($st, &value);
    $ret = $341;
  }
  if ($ret == 0) {
    $377 = value;
    if ($377 >= 0) {
      $343 = 1;
    } else {
      $343 = (_Bool) !$specs;
    }
    if ($343) {
      $344 = 1;
    } else {
      $376 = (*$specs).field_unsigned;
      $344 = (_Bool) !$376;
    }
    if ($344) {
      $375 = value;
      $346 = INTEGER_map_value2enum($specs, $375);
      $345 = (void *) $346;
    } else {
      $345 = (void *) (void *) 0;
    }
    $el = $345;
    if ($el) {
      if ($plainOrXER == 0) {
        $373 = value;
        $374 = (*$el).enum_name;
        $347 =
          asn__format_to_callback
          ($cb, $app_key, __stringlit_5, $373, $374);
        return $347;
      } else {
        $372 = (*$el).enum_name;
        $348 = asn__format_to_callback($cb, $app_key, __stringlit_4, $372);
        return $348;
      }
    } else {
      if ($plainOrXER) {
        $353 = (_Bool) $specs;
      } else {
        $353 = 0;
      }
      if ($353) {
        $371 = (*$specs).strict_enumeration;
        $354 = (_Bool) $371;
      } else {
        $354 = 0;
      }
      if ($354) {
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        $349 = __errno_location();
        *$349 = 1;
        return -1;
      } else {
        if ($specs) {
          $370 = (*$specs).field_unsigned;
          $350 = (_Bool) $370;
        } else {
          $350 = 0;
        }
        if ($350) {
          $351 = (signed char *) __stringlit_3;
        } else {
          $351 = (signed char *) __stringlit_2;
        }
        $369 = value;
        $352 = asn__format_to_callback($cb, $app_key, $351, $369);
        return $352;
      }
    }
  } else {
    if ($plainOrXER) {
      $356 = (_Bool) $specs;
    } else {
      $356 = 0;
    }
    if ($356) {
      $368 = (*$specs).strict_enumeration;
      $357 = (_Bool) $368;
    } else {
      $357 = 0;
    }
    if ($357) {
      for (; 1; ({ break; })) {
        /*skip*/;
      }
      $355 = __errno_location();
      *$355 = 1;
      return -1;
    }
  }
  $p = scratch;
  for (; 1; $buf = $buf + 1) {
    if (! ($buf < $buf_end)) {
      break;
    }
    $h2c = __stringlit_6;
    if ($p - scratch >= (int) (sizeof(signed char [32]) - 4)) {
      $358 = $cb(scratch, $p - scratch, $app_key);
      if ($358 < 0) {
        return -1;
      }
      $wrote = $wrote + ($p - scratch);
      $p = scratch;
    }
    $359 = $p;
    $p = $359 + 1;
    $366 = *$buf;
    $367 = *($h2c + ($366 >> 4));
    *$359 = $367;
    $360 = $p;
    $p = $360 + 1;
    $364 = *$buf;
    $365 = *($h2c + ($364 & 15));
    *$360 = $365;
    $361 = $p;
    $p = $361 + 1;
    *$361 = 58;
  }
  if ($p != scratch) {
    $p = $p - 1;
  }
  $wrote = $wrote + ($p - scratch);
  $362 = $cb(scratch, $p - scratch, $app_key);
  if ($362 < 0) {
    $363 = (int) -1;
  } else {
    $363 = (int) $wrote;
  }
  return $363;
}

int INTEGER_print(struct asn_TYPE_descriptor_s *$td, void *$sptr, int $ilevel, int (*$cb)(void *, unsigned int, void *), void *$app_key)
{
  register struct ASN__PRIMITIVE_TYPE_s *$st;
  register int $ret;
  register int $343;
  register int $342;
  register int $341;
  register int $340;
  register unsigned char *$344;
  $st = (struct ASN__PRIMITIVE_TYPE_s *) $sptr;
  if (!$st) {
    $342 = 1;
  } else {
    $344 = (*$st).buf;
    $342 = (_Bool) !$344;
  }
  if ($342) {
    $340 = $cb(__stringlit_7, 8, $app_key);
    $ret = $340;
  } else {
    $341 = INTEGER__dump($td, $st, $cb, $app_key, 0);
    $ret = $341;
  }
  if ($ret < 0) {
    $343 = (int) -1;
  } else {
    $343 = (int) 0;
  }
  return $343;
}

int INTEGER__compar_enum2value(void *$kp, void *$am)
{
  register struct e2v_key *$key;
  register struct asn_INTEGER_enum_map_s *$el;
  register signed char *$ptr;
  register signed char *$end;
  register signed char *$name;
  register int $341;
  register int $340;
  register unsigned int $351;
  register struct asn_INTEGER_enum_map_s *$350;
  register unsigned int *$349;
  register struct asn_INTEGER_enum_map_s *$348;
  register signed char $347;
  register signed char $346;
  register signed char $345;
  register unsigned char $344;
  register unsigned char $343;
  register signed char $342;
  $key = (struct e2v_key *) $kp;
  $el = (struct asn_INTEGER_enum_map_s *) $am;
  $348 = (*$key).vemap;
  $349 = (*$key).evmap;
  $350 = (*$key).vemap;
  $351 = *($349 + ($el - $350));
  $el = $348 + $351;
  $ptr = (*$key).start;
  $end = (*$key).stop;
  $name = (*$el).enum_name;
  for (; 1; $ptr = $ptr + 1, $name = $name + 1) {
    if (! ($ptr < $end)) {
      break;
    }
    $345 = *$ptr;
    $346 = *$name;
    if ($345 != $346) {
      $340 = 1;
    } else {
      $347 = *$name;
      $340 = (_Bool) !$347;
    }
    if ($340) {
      $343 = *((unsigned char *) $ptr);
      $344 = *((unsigned char *) $name);
      return $343 - $344;
    }
  }
  $342 = *($name + 0);
  if ($342) {
    $341 = (int) -1;
  } else {
    $341 = (int) 0;
  }
  return $341;
}

struct asn_INTEGER_enum_map_s *INTEGER_map_enum2value(struct asn_INTEGER_specifics_s *$specs, signed char *$lstart, signed char *$lstop)
{
  struct e2v_key key;
  register struct asn_INTEGER_enum_map_s *$el_found;
  register int $count;
  register signed char *$lp;
  register void *$341;
  register int $340;
  register int $350;
  register signed char $349;
  register struct asn_INTEGER_enum_map_s *$348;
  register unsigned int *$347;
  register struct asn_INTEGER_enum_map_s *$346;
  register unsigned int $345;
  register struct asn_INTEGER_enum_map_s *$344;
  register unsigned int *$343;
  register struct asn_INTEGER_enum_map_s *$342;
  if ($specs) {
    $350 = (*$specs).map_count;
    $340 = (int) $350;
  } else {
    $340 = (int) 0;
  }
  $count = $340;
  if (!$count) {
    return (void *) 0;
  }
  $lstart = $lstart + 1;
  $lp = $lstart;
  for (; 1; $lp = $lp + 1) {
    if (! ($lp < $lstop)) {
      break;
    }
    $349 = *$lp;
    switch ($349) {
      case 9:
      case 10:
      case 11:
      case 12:
      case 13:
      case 32:
      case 47:
      case 62:
        break;
      default:
        continue;
      
    }
    break;
  }
  if ($lp == $lstop) {
    return (void *) 0;
  }
  $lstop = $lp;
  key.start = $lstart;
  key.stop = $lstop;
  $348 = (*$specs).value2enum;
  key.vemap = $348;
  $347 = (*$specs).enum2value;
  key.evmap = $347;
  $346 = (*$specs).value2enum;
  $341 =
    bsearch
    (&key, $346, $count, sizeof(struct asn_INTEGER_enum_map_s),
     INTEGER__compar_enum2value);
  $el_found = (struct asn_INTEGER_enum_map_s *) $341;
  if ($el_found) {
    $342 = key.vemap;
    $343 = key.evmap;
    $344 = key.vemap;
    $345 = *($343 + ($el_found - $344));
    $el_found = $342 + $345;
  }
  return $el_found;
}

int INTEGER__compar_value2enum(void *$kp, void *$am)
{
  register int $a;
  register struct asn_INTEGER_enum_map_s *$el;
  register int $b;
  $a = *((int *) $kp);
  $el = (struct asn_INTEGER_enum_map_s *) $am;
  $b = (*$el).nat_value;
  if ($a < $b) {
    return -1;
  } else {
    if ($a == $b) {
      return 0;
    } else {
      return 1;
    }
  }
}

struct asn_INTEGER_enum_map_s *INTEGER_map_value2enum(struct asn_INTEGER_specifics_s *$specs, int $value)
{
  int value;
  register int $count;
  register void *$341;
  register int $340;
  register int $343;
  register struct asn_INTEGER_enum_map_s *$342;
  value = $value;
  if ($specs) {
    $343 = (*$specs).map_count;
    $340 = (int) $343;
  } else {
    $340 = (int) 0;
  }
  $count = $340;
  if (!$count) {
    return 0;
  }
  $342 = (*$specs).value2enum;
  $341 =
    bsearch
    (&value, $342, $count, sizeof(struct asn_INTEGER_enum_map_s),
     INTEGER__compar_value2enum);
  return (struct asn_INTEGER_enum_map_s *) $341;
}

int INTEGER_st_prealloc(struct ASN__PRIMITIVE_TYPE_s *$st, int $min_size)
{
  register void *$p;
  register void *$b;
  register void *$340;
  $340 = malloc($min_size + 1);
  $p = $340;
  if ($p) {
    $b = (*$st).buf;
    (*$st).size = 0;
    (*$st).buf = $p;
    free($b);
    return 0;
  } else {
    return -1;
  }
}

int INTEGER__xer_body_decode(struct asn_TYPE_descriptor_s *$td, void *$sptr, void *$chunk_buf, unsigned int $chunk_size)
{
  long long dec_value;
  signed char *dec_value_end;
  register struct ASN__PRIMITIVE_TYPE_s *$st;
  register long long $hex_value;
  register signed char *$lp;
  register signed char *$lstart;
  register signed char *$lstop;
  register int $state;
  register signed char *$dec_value_start;
  register int $lv;
  register struct asn_INTEGER_enum_map_s *$el;
  register int $348;
  register int $347;
  register int $346;
  register unsigned int $345;
  register int $344;
  register int $343;
  register struct asn_INTEGER_enum_map_s *$342;
  register unsigned int $341;
  register int $340;
  register unsigned char *$357;
  register void *$356;
  register int $355;
  register unsigned char *$354;
  register long long $353;
  register long long $352;
  register unsigned int $351;
  register unsigned char *$350;
  register long long $349;
  $st = (struct ASN__PRIMITIVE_TYPE_s *) $sptr;
  $hex_value = (long long) 0;
  $lstart = (signed char *) $chunk_buf;
  $lstop = $lstart + $chunk_size;
  $state = 0;
  $dec_value_start = 0;
  dec_value_end = 0;
  if ($chunk_size) {
    for (; 1; ({ break; })) {
      /*skip*/;
    }
  }
  $340 = INTEGER_st_prealloc($st, $chunk_size / 3 + 1);
  if ($340) {
    return 0;
  }
  $lp = $lstart;
  for (; 1; $lp = $lp + 1) {
    if (! ($lp < $lstop)) {
      break;
    }
    $lv = *$lp;
    switch ($lv) {
      case 9:
      case 10:
      case 13:
      case 32:
        switch ($state) {
          case 0:
          case 4:
          case 7:
          case 1:
            continue;
          case 3:
            dec_value_end = $lp;
            $state = 4;
            continue;
          case 8:
            $state = 7;
            continue;
          default:
            break;
          
        }
        break;
      case 45:
        if ($state == 0) {
          dec_value = 0;
          $dec_value_start = $lp;
          $state = 2;
          continue;
        }
        break;
      case 43:
        if ($state == 0) {
          dec_value = 0;
          $dec_value_start = $lp;
          $state = 2;
          continue;
        }
        break;
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
        switch ($state) {
          case 3:
            continue;
          case 1:
          case 5:
            $hex_value = (long long) ($lv - 48 << 4);
            $state = 6;
            continue;
          case 6:
            $hex_value = $hex_value + ($lv - 48);
            $state = 8;
            $341 = (*$st).size;
            (*$st).size = $341 + 1;
            $357 = (*$st).buf;
            *($357 + $341) = (unsigned char) $hex_value;
            continue;
          case 8:
            return 2;
          case 0:
            dec_value = 0;
            $dec_value_start = $lp;
          case 2:
            $state = 3;
            continue;
          default:
            break;
          
        }
        break;
      case 60:
        if ($state == 0) {
          $356 = (*$td).specifics;
          $342 =
            INTEGER_map_enum2value
            ((struct asn_INTEGER_specifics_s *) $356, $lstart, $lstop);
          $el = $342;
          if ($el) {
            for (; 1; ({ break; })) {
              /*skip*/;
            }
            $355 = (*$el).nat_value;
            dec_value = $355;
            $state = 9;
            $lp = $lstop - 1;
            continue;
          }
          for (; 1; ({ break; })) {
            /*skip*/;
          }
        }
        return 2;
      case 58:
        if ($state == 8) {
          $state = 5;
          continue;
        } else {
          if ($state == 3) {
            for (; 1; ({ break; })) {
              /*skip*/;
            }
            $state = 1;
            $dec_value_start = 0;
            $lp = $lstart - 1;
            continue;
          } else {
            for (; 1; ({ break; })) {
              /*skip*/;
            }
            break;
          }
        }
      case 65:
      case 66:
      case 67:
      case 68:
      case 69:
      case 70:
      case 97:
      case 98:
      case 99:
      case 100:
      case 101:
      case 102:
        switch ($state) {
          case 1:
          case 0:
          case 5:
            if ($lv < 97) {
              $343 = (int) 65;
            } else {
              $343 = (int) 97;
            }
            $hex_value = (long long) ($lv - $343);
            $hex_value = $hex_value + 10;
            $hex_value = $hex_value << 4;
            $state = 6;
            continue;
          case 6:
            if ($lv < 97) {
              $344 = (int) 65;
            } else {
              $344 = (int) 97;
            }
            $hex_value = $hex_value + ($lv - $344);
            $hex_value = $hex_value + 10;
            $345 = (*$st).size;
            (*$st).size = $345 + 1;
            $354 = (*$st).buf;
            *($354 + $345) = (unsigned char) $hex_value;
            $state = 8;
            continue;
          case 3:
            for (; 1; ({ break; })) {
              /*skip*/;
            }
            $state = 1;
            $dec_value_start = 0;
            $lp = $lstart - 1;
            continue;
          default:
            break;
          
        }
        break;
      
    }
    for (; 1; ({ break; })) {
      /*skip*/;
    }
    $state = 10;
    break;
  }
  switch ($state) {
    case 9:
      break;
    case 3:
      dec_value_end = $lstop;
    case 4:
      $346 = asn_strtoimax_lim($dec_value_start, &dec_value_end, &dec_value);
      switch ($346) {
        case 0:
          $352 = dec_value;
          if ($352 >= -2147483647 - 1) {
            $353 = dec_value;
            $347 = (_Bool) ($353 <= 2147483647);
          } else {
            $347 = 0;
          }
          if ($347) {
            break;
          } else {
            for (; 1; ({ break; })) {
              /*skip*/;
            }
          }
        case 4294967293:
          for (; 1; ({ break; })) {
            /*skip*/;
          }
          return 1;
        case 4294967294:
        case 4294967295:
        case 1:
          return 2;
        
      }
      break;
    case 8:
    case 7:
      $350 = (*$st).buf;
      $351 = (*$st).size;
      *($350 + $351) = 0;
      return 4;
    case 5:
    case 6:
    case 1:
      return 2;
    case 0:
      return 3;
    case 2:
    case 10:
      for (; 1; ({ break; })) {
        /*skip*/;
      }
      return 2;
    
  }
  $349 = dec_value;
  $348 = asn_imax2INTEGER($st, $349);
  if ($348) {
    for (; 1; ({ break; })) {
      /*skip*/;
    }
    return 0;
  }
  return 4;
}

void INTEGER_decode_xer(struct asn_dec_rval_s *$_res, struct asn_codec_ctx_s *$opt_codec_ctx, struct asn_TYPE_descriptor_s *$td, void **$sptr, signed char *$opt_mname, void *$buf_ptr, unsigned int $size)
{
  struct asn_dec_rval_s _res__1;
  xer_decode_primitive
    (&_res__1, $opt_codec_ctx, $td, $sptr,
     sizeof(struct ASN__PRIMITIVE_TYPE_s), $opt_mname, $buf_ptr, $size,
     INTEGER__xer_body_decode);
  *$_res = _res__1;
  return;
}

void INTEGER_encode_xer(struct asn_enc_rval_s *$_res, struct asn_TYPE_descriptor_s *$td, void *$sptr, int $ilevel, int $flags, int (*$cb)(void *, unsigned int, void *), void *$app_key)
{
  struct asn_enc_rval_s er;
  struct asn_enc_rval_s tmp_error;
  struct asn_enc_rval_s tmp_error__1;
  register struct ASN__PRIMITIVE_TYPE_s *$st;
  register int $341;
  register int $340;
  register unsigned char *$343;
  register int $342;
  $st = (struct ASN__PRIMITIVE_TYPE_s *) $sptr;
  if (!$st) {
    $340 = 1;
  } else {
    $343 = (*$st).buf;
    $340 = (_Bool) !$343;
  }
  if ($340) {
    for (; 1; ({ break; })) {
      tmp_error.encoded = -1;
      tmp_error.failed_type = $td;
      tmp_error.structure_ptr = $sptr;
      for (; 1; ({ break; })) {
        /*skip*/;
      }
      *$_res = tmp_error;
      return;
    }
  }
  $341 = INTEGER__dump($td, $st, $cb, $app_key, 1);
  er.encoded = $341;
  $342 = er.encoded;
  if ($342 < 0) {
    for (; 1; ({ break; })) {
      tmp_error__1.encoded = -1;
      tmp_error__1.failed_type = $td;
      tmp_error__1.structure_ptr = $sptr;
      for (; 1; ({ break; })) {
        /*skip*/;
      }
      *$_res = tmp_error__1;
      return;
    }
  }
  for (; 1; ({ break; })) {
    er.structure_ptr = 0;
    er.failed_type = 0;
    *$_res = er;
    return;
  }
}

void INTEGER_decode_uper(struct asn_dec_rval_s *$_res, struct asn_codec_ctx_s *$opt_codec_ctx, struct asn_TYPE_descriptor_s *$td, struct asn_per_constraints_s *$constraints, void **$sptr, struct asn_bit_data_s *$pd)
{
  struct asn_dec_rval_s rval;
  int repeat;
  struct asn_dec_rval_s tmp_error;
  struct asn_dec_rval_s tmp_error__1;
  struct asn_dec_rval_s tmp_error__2;
  struct asn_dec_rval_s tmp_error__3;
  struct asn_dec_rval_s tmp_error__4;
  unsigned int uvalue;
  struct asn_dec_rval_s tmp_error__5;
  struct asn_dec_rval_s tmp_error__6;
  unsigned int uvalue__1;
  int svalue;
  struct asn_dec_rval_s tmp_error__7;
  struct asn_dec_rval_s tmp_error__8;
  struct asn_dec_rval_s tmp_error__9;
  struct asn_dec_rval_s tmp_error__10;
  struct asn_dec_rval_s tmp_error__11;
  int value;
  struct asn_dec_rval_s tmp_error__12;
  struct asn_dec_rval_s tmp_error__13;
  register struct asn_INTEGER_specifics_s *$specs;
  register struct ASN__PRIMITIVE_TYPE_s *$st;
  register struct asn_per_constraint_s *$ct;
  register int $inext;
  register unsigned int $size;
  register int $len;
  register void *$p;
  register int $ret;
  register int $361;
  register int $360;
  register int $359;
  register int $358;
  register void *$357;
  register int $356;
  register int $355;
  register int $354;
  register int $353;
  register int $352;
  register int $351;
  register int $350;
  register int $349;
  register int $348;
  register int $347;
  register void *$346;
  register void *$345;
  register int $344;
  register int $343;
  register void *$342;
  register void *$341;
  register void *$340;
  register void *$395;
  register void *$394;
  register int $393;
  register unsigned char *$392;
  register unsigned char *$391;
  register int $390;
  register int $389;
  register int $388;
  register unsigned char *$387;
  register int $386;
  register int $385;
  register int $384;
  register int $383;
  register int $382;
  register int $381;
  register unsigned int $380;
  register unsigned int $379;
  register int $378;
  register int $377;
  register int $376;
  register unsigned int $375;
  register int $374;
  register int $373;
  register unsigned int $372;
  register unsigned char *$371;
  register unsigned int $370;
  register unsigned char *$369;
  register unsigned int $368;
  register int $367;
  register unsigned int $366;
  register unsigned char *$365;
  register int $364;
  register int $363;
  register int $362;
  $395 = (*$td).specifics;
  $specs = (struct asn_INTEGER_specifics_s *) $395;
  rval.code = 0;
  rval.consumed = 0;
  $394 = *$sptr;
  $st = (struct ASN__PRIMITIVE_TYPE_s *) $394;
  if (!$st) {
    $340 = calloc(1, sizeof(struct ASN__PRIMITIVE_TYPE_s));
    $341 = (void *) $340;
    *$sptr = $341;
    $st = (struct ASN__PRIMITIVE_TYPE_s *) $341;
    if (!$st) {
      for (; 1; ({ break; })) {
        tmp_error.code = 2;
        tmp_error.consumed = 0;
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        *$_res = tmp_error;
        return;
      }
    }
  }
  if (!$constraints) {
    $constraints = (*$td).encoding_constraints.per_constraints;
  }
  if ($constraints) {
    $342 = (void *) &(*$constraints).value;
  } else {
    $342 = (void *) (void *) 0;
  }
  $ct = $342;
  if ($ct) {
    $393 = (*$ct).flags;
    $344 = (_Bool) ($393 & 4);
  } else {
    $344 = 0;
  }
  if ($344) {
    $343 = asn_get_few_bits($pd, 1);
    $inext = $343;
    if ($inext < 0) {
      for (; 1; ({ break; })) {
        tmp_error__1.code = 1;
        tmp_error__1.consumed = 0;
        *$_res = tmp_error__1;
        return;
      }
    }
    if ($inext) {
      $ct = 0;
    }
  }
  $392 = (*$st).buf;
  free($392);
  (*$st).buf = 0;
  (*$st).size = 0;
  if ($ct) {
    $386 = (*$ct).flags;
    if ($386 & 1) {
      $345 = calloc(1, 2);
      (*$st).buf = (unsigned char *) $345;
      $391 = (*$st).buf;
      if (!$391) {
        for (; 1; ({ break; })) {
          tmp_error__2.code = 2;
          tmp_error__2.consumed = 0;
          for (; 1; ({ break; })) {
            /*skip*/;
          }
          *$_res = tmp_error__2;
          return;
        }
      }
      (*$st).size = 1;
    } else {
      $389 = (*$ct).flags;
      if ($389 & 2) {
        $390 = (*$ct).range_bits;
        $347 = (_Bool) ($390 >= 0);
      } else {
        $347 = 0;
      }
      if ($347) {
        $388 = (*$ct).range_bits;
        $size = $388 + 7 >> 3;
        $346 = malloc(1 + $size + 1);
        (*$st).buf = (unsigned char *) $346;
        $387 = (*$st).buf;
        if (!$387) {
          for (; 1; ({ break; })) {
            tmp_error__3.code = 2;
            tmp_error__3.consumed = 0;
            for (; 1; ({ break; })) {
              /*skip*/;
            }
            *$_res = tmp_error__3;
            return;
          }
        }
        (*$st).size = $size;
      }
    }
  }
  if ($ct) {
    $385 = (*$ct).flags;
    $355 = (_Bool) ($385 != 0);
  } else {
    $355 = 0;
  }
  if ($355) {
    for (; 1; ({ break; })) {
      /*skip*/;
    }
    $373 = (*$ct).range_bits;
    if ($373 >= 0) {
      $384 = (*$ct).range_bits;
      if ((unsigned int) $384 > 8 * sizeof(unsigned int)) {
        for (; 1; ({ break; })) {
          tmp_error__4.code = 2;
          tmp_error__4.consumed = 0;
          for (; 1; ({ break; })) {
            /*skip*/;
          }
          *$_res = tmp_error__4;
          return;
        }
      }
      if ($specs) {
        $383 = (*$specs).field_unsigned;
        $354 = (_Bool) $383;
      } else {
        $354 = 0;
      }
      if ($354) {
        uvalue = 0;
        $382 = (*$ct).range_bits;
        $348 = uper_get_constrained_whole_number($pd, &uvalue, $382);
        if ($348) {
          for (; 1; ({ break; })) {
            tmp_error__5.code = 1;
            tmp_error__5.consumed = 0;
            *$_res = tmp_error__5;
            return;
          }
        }
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        $380 = uvalue;
        $381 = (*$ct).lower_bound;
        uvalue = $380 + $381;
        $379 = uvalue;
        $349 = asn_ulong2INTEGER($st, $379);
        if ($349) {
          for (; 1; ({ break; })) {
            tmp_error__6.code = 2;
            tmp_error__6.consumed = 0;
            for (; 1; ({ break; })) {
              /*skip*/;
            }
            *$_res = tmp_error__6;
            return;
          }
        }
      } else {
        uvalue__1 = 0;
        $378 = (*$ct).range_bits;
        $350 = uper_get_constrained_whole_number($pd, &uvalue__1, $378);
        if ($350) {
          for (; 1; ({ break; })) {
            tmp_error__7.code = 1;
            tmp_error__7.consumed = 0;
            *$_res = tmp_error__7;
            return;
          }
        }
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        $375 = uvalue__1;
        $376 = (*$ct).lower_bound;
        $377 = (*$ct).upper_bound;
        $351 = per_long_range_unrebase($375, $376, $377, &svalue);
        if ($351) {
          $352 = 1;
        } else {
          $374 = svalue;
          $353 = asn_long2INTEGER($st, $374);
          $352 = (_Bool) $353;
        }
        if ($352) {
          for (; 1; ({ break; })) {
            tmp_error__8.code = 2;
            tmp_error__8.consumed = 0;
            for (; 1; ({ break; })) {
              /*skip*/;
            }
            *$_res = tmp_error__8;
            return;
          }
        }
      }
      *$_res = rval;
      return;
    }
  } else {
    for (; 1; ({ break; })) {
      /*skip*/;
    }
  }
  for (; 1; $367 = repeat, ({ if (! $367) {
                                break;
                              } })) {
    $len = 0;
    $p = (void *) 0;
    $ret = 0;
    $356 = uper_get_length($pd, -1, 0, &repeat);
    $len = $356;
    if ($len < 0) {
      for (; 1; ({ break; })) {
        tmp_error__9.code = 1;
        tmp_error__9.consumed = 0;
        *$_res = tmp_error__9;
        return;
      }
    }
    $371 = (*$st).buf;
    $372 = (*$st).size;
    $357 = realloc($371, $372 + $len + 1);
    $p = $357;
    if (!$p) {
      for (; 1; ({ break; })) {
        tmp_error__10.code = 2;
        tmp_error__10.consumed = 0;
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        *$_res = tmp_error__10;
        return;
      }
    }
    (*$st).buf = (unsigned char *) $p;
    $369 = (*$st).buf;
    $370 = (*$st).size;
    $358 = asn_get_many_bits($pd, $369 + $370, 0, 8 * $len);
    $ret = $358;
    if ($ret < 0) {
      for (; 1; ({ break; })) {
        tmp_error__11.code = 1;
        tmp_error__11.consumed = 0;
        *$_res = tmp_error__11;
        return;
      }
    }
    $368 = (*$st).size;
    (*$st).size = $368 + $len;
  }
  $365 = (*$st).buf;
  $366 = (*$st).size;
  *($365 + $366) = 0;
  if ($ct) {
    $364 = (*$ct).lower_bound;
    $361 = (_Bool) $364;
  } else {
    $361 = 0;
  }
  if ($361) {
    value = 0;
    $359 = asn_INTEGER2long($st, &value);
    if ($359) {
      for (; 1; ({ break; })) {
        tmp_error__12.code = 2;
        tmp_error__12.consumed = 0;
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        *$_res = tmp_error__12;
        return;
      }
    }
    $362 = value;
    $363 = (*$ct).lower_bound;
    $360 = asn_imax2INTEGER($st, $362 + $363);
    if ($360) {
      for (; 1; ({ break; })) {
        tmp_error__13.code = 2;
        tmp_error__13.consumed = 0;
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        *$_res = tmp_error__13;
        return;
      }
    }
  }
  *$_res = rval;
  return;
}

void INTEGER_encode_uper(struct asn_enc_rval_s *$_res, struct asn_TYPE_descriptor_s *$td, struct asn_per_constraints_s *$constraints, void *$sptr, struct asn_bit_outp_s *$po)
{
  struct asn_enc_rval_s er;
  int value;
  struct asn_enc_rval_s tmp_error;
  unsigned int uval;
  struct asn_enc_rval_s tmp_error__1;
  struct asn_enc_rval_s tmp_error__2;
  struct asn_enc_rval_s tmp_error__3;
  struct asn_enc_rval_s tmp_error__4;
  unsigned int v;
  struct asn_enc_rval_s tmp_error__5;
  struct asn_enc_rval_s tmp_error__6;
  struct asn_enc_rval_s tmp_error__7;
  int need_eom;
  struct asn_enc_rval_s tmp_error__8;
  struct asn_enc_rval_s tmp_error__9;
  struct asn_enc_rval_s tmp_error__10;
  register struct asn_INTEGER_specifics_s *$specs;
  register struct ASN__PRIMITIVE_TYPE_s *$st;
  register unsigned char *$buf;
  register unsigned char *$end;
  register struct asn_per_constraint_s *$ct;
  register int $inext;
  register int $mayEncode;
  register int $355;
  register int $354;
  register int $353;
  register int $352;
  register int $351;
  register int $350;
  register int $349;
  register int $348;
  register int $347;
  register int $346;
  register int $345;
  register int $344;
  register int $343;
  register int $342;
  register void *$341;
  register int $340;
  register void *$386;
  register unsigned int $385;
  register int $384;
  register int $383;
  register unsigned int $382;
  register int $381;
  register unsigned int $380;
  register int $379;
  register unsigned int $378;
  register int $377;
  register int $376;
  register unsigned int $375;
  register int $374;
  register int $373;
  register int $372;
  register int $371;
  register int $370;
  register int $369;
  register int $368;
  register int $367;
  register int $366;
  register int $365;
  register int $364;
  register int $363;
  register int $362;
  register int $361;
  register unsigned int $360;
  register int $359;
  register unsigned int $358;
  register unsigned char *$357;
  register int $356;
  $386 = (*$td).specifics;
  $specs = (struct asn_INTEGER_specifics_s *) $386;
  $st = (struct ASN__PRIMITIVE_TYPE_s *) $sptr;
  value = 0;
  if (!$st) {
    $340 = 1;
  } else {
    $385 = (*$st).size;
    $340 = (_Bool) ($385 == 0);
  }
  if ($340) {
    for (; 1; ({ break; })) {
      tmp_error.encoded = -1;
      tmp_error.failed_type = $td;
      tmp_error.structure_ptr = $sptr;
      for (; 1; ({ break; })) {
        /*skip*/;
      }
      *$_res = tmp_error;
      return;
    }
  }
  if (!$constraints) {
    $constraints = (*$td).encoding_constraints.per_constraints;
  }
  if ($constraints) {
    $341 = (void *) &(*$constraints).value;
  } else {
    $341 = (void *) (void *) 0;
  }
  $ct = $341;
  er.encoded = 0;
  if ($ct) {
    $inext = 0;
    if ($specs) {
      $384 = (*$specs).field_unsigned;
      $346 = (_Bool) $384;
    } else {
      $346 = 0;
    }
    if ($346) {
      $342 = asn_INTEGER2ulong($st, &uval);
      if ($342) {
        for (; 1; ({ break; })) {
          tmp_error__1.encoded = -1;
          tmp_error__1.failed_type = $td;
          tmp_error__1.structure_ptr = $sptr;
          for (; 1; ({ break; })) {
            /*skip*/;
          }
          *$_res = tmp_error__1;
          return;
        }
      }
      $376 = (*$ct).flags;
      if ($376 & 1) {
        $382 = uval;
        $383 = (*$ct).lower_bound;
        if ($382 < (unsigned int) $383) {
          $inext = 1;
        }
      } else {
        $377 = (*$ct).range_bits;
        if ($377 >= 0) {
          $378 = uval;
          $379 = (*$ct).lower_bound;
          if ($378 < (unsigned int) $379) {
            $343 = 1;
          } else {
            $380 = uval;
            $381 = (*$ct).upper_bound;
            $343 = (_Bool) ($380 > (unsigned int) $381);
          }
          if ($343) {
            $inext = 1;
          }
        }
      }
      for (; 1; ({ break; })) {
        /*skip*/;
      }
      $375 = uval;
      value = $375;
    } else {
      $344 = asn_INTEGER2long($st, &value);
      if ($344) {
        for (; 1; ({ break; })) {
          tmp_error__2.encoded = -1;
          tmp_error__2.failed_type = $td;
          tmp_error__2.structure_ptr = $sptr;
          for (; 1; ({ break; })) {
            /*skip*/;
          }
          *$_res = tmp_error__2;
          return;
        }
      }
      $367 = (*$ct).flags;
      if ($367 & 1) {
        $373 = value;
        $374 = (*$ct).lower_bound;
        if ($373 < $374) {
          $inext = 1;
        }
      } else {
        $368 = (*$ct).range_bits;
        if ($368 >= 0) {
          $369 = value;
          $370 = (*$ct).lower_bound;
          if ($369 < $370) {
            $345 = 1;
          } else {
            $371 = value;
            $372 = (*$ct).upper_bound;
            $345 = (_Bool) ($371 > $372);
          }
          if ($345) {
            $inext = 1;
          }
        }
      }
      for (; 1; ({ break; })) {
        /*skip*/;
      }
    }
    $366 = (*$ct).flags;
    if ($366 & 4) {
      $347 = asn_put_few_bits($po, $inext, 1);
      if ($347) {
        for (; 1; ({ break; })) {
          tmp_error__3.encoded = -1;
          tmp_error__3.failed_type = $td;
          tmp_error__3.structure_ptr = $sptr;
          for (; 1; ({ break; })) {
            /*skip*/;
          }
          *$_res = tmp_error__3;
          return;
        }
      }
      if ($inext) {
        $ct = 0;
      }
    } else {
      if ($inext) {
        for (; 1; ({ break; })) {
          tmp_error__4.encoded = -1;
          tmp_error__4.failed_type = $td;
          tmp_error__4.structure_ptr = $sptr;
          for (; 1; ({ break; })) {
            /*skip*/;
          }
          *$_res = tmp_error__4;
          return;
        }
      }
    }
  }
  if ($ct) {
    $365 = (*$ct).range_bits;
    $350 = (_Bool) ($365 >= 0);
  } else {
    $350 = 0;
  }
  if ($350) {
    for (; 1; ({ break; })) {
      /*skip*/;
    }
    $362 = value;
    $363 = (*$ct).lower_bound;
    $364 = (*$ct).upper_bound;
    $348 = per_long_range_rebase($362, $363, $364, &v);
    if ($348) {
      for (; 1; ({ break; })) {
        tmp_error__5.encoded = -1;
        tmp_error__5.failed_type = $td;
        tmp_error__5.structure_ptr = $sptr;
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        *$_res = tmp_error__5;
        return;
      }
    }
    $360 = v;
    $361 = (*$ct).range_bits;
    $349 = uper_put_constrained_whole_number_u($po, $360, $361);
    if ($349) {
      for (; 1; ({ break; })) {
        tmp_error__6.encoded = -1;
        tmp_error__6.failed_type = $td;
        tmp_error__6.structure_ptr = $sptr;
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        *$_res = tmp_error__6;
        return;
      }
    }
    for (; 1; ({ break; })) {
      er.structure_ptr = 0;
      er.failed_type = 0;
      *$_res = er;
      return;
    }
  }
  if ($ct) {
    $359 = (*$ct).lower_bound;
    $351 = (_Bool) $359;
  } else {
    $351 = 0;
  }
  if ($351) {
    for (; 1; ({ break; })) {
      /*skip*/;
    }
    for (; 1; ({ break; })) {
      tmp_error__7.encoded = -1;
      tmp_error__7.failed_type = $td;
      tmp_error__7.structure_ptr = $sptr;
      for (; 1; ({ break; })) {
        /*skip*/;
      }
      *$_res = tmp_error__7;
      return;
    }
  }
  $buf = (*$st).buf;
  $357 = (*$st).buf;
  $358 = (*$st).size;
  $end = $357 + $358;
  while (1) {
    if (! ($buf < $end)) {
      break;
    }
    need_eom = 0;
    $352 = uper_put_length($po, $end - $buf, &need_eom);
    $mayEncode = $352;
    if ($mayEncode < 0) {
      for (; 1; ({ break; })) {
        tmp_error__8.encoded = -1;
        tmp_error__8.failed_type = $td;
        tmp_error__8.structure_ptr = $sptr;
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        *$_res = tmp_error__8;
        return;
      }
    }
    $353 = asn_put_many_bits($po, $buf, 8 * $mayEncode);
    if ($353) {
      for (; 1; ({ break; })) {
        tmp_error__9.encoded = -1;
        tmp_error__9.failed_type = $td;
        tmp_error__9.structure_ptr = $sptr;
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        *$_res = tmp_error__9;
        return;
      }
    }
    $buf = $buf + $mayEncode;
    $356 = need_eom;
    if ($356) {
      $355 = uper_put_length($po, 0, 0);
      $354 = (_Bool) $355;
    } else {
      $354 = 0;
    }
    if ($354) {
      for (; 1; ({ break; })) {
        tmp_error__10.encoded = -1;
        tmp_error__10.failed_type = $td;
        tmp_error__10.structure_ptr = $sptr;
        for (; 1; ({ break; })) {
          /*skip*/;
        }
        *$_res = tmp_error__10;
        return;
      }
    }
  }
  for (; 1; ({ break; })) {
    er.structure_ptr = 0;
    er.failed_type = 0;
    *$_res = er;
    return;
  }
}

long long asn__integer_convert(unsigned char *$b, unsigned char *$end)
{
  register unsigned long long $value;
  register unsigned char $341;
  register unsigned char $340;
  $341 = *$b;
  if ($341 >> 7) {
    $value = (unsigned long long) -1;
  } else {
    $value = (unsigned long long) 0;
  }
  for (; 1; $b = $b + 1) {
    if (! ($b < $end)) {
      break;
    }
    $340 = *$b;
    $value = $value << 8 | $340;
  }
  return $value;
}

int asn_INTEGER2imax(struct ASN__PRIMITIVE_TYPE_s *$iptr, long long *$lptr)
{
  register unsigned char *$b;
  register unsigned char *$end;
  register unsigned int $size;
  register unsigned char *$end1;
  register long long $344;
  register int *$343;
  register int $342;
  register int $341;
  register int *$340;
  register unsigned char *$348;
  register unsigned char $347;
  register unsigned char $346;
  register unsigned char $345;
  if (!$iptr) {
    $341 = 1;
  } else {
    $348 = (*$iptr).buf;
    $341 = (_Bool) !$348;
  }
  if ($341) {
    $342 = 1;
  } else {
    $342 = (_Bool) !$lptr;
  }
  if ($342) {
    $340 = __errno_location();
    *$340 = 22;
    return -1;
  }
  $b = (*$iptr).buf;
  $size = (*$iptr).size;
  $end = $b + $size;
  if ($size > sizeof(long long)) {
    $end1 = $end - 1;
    for (; 1; $b = $b + 1) {
      if (! ($b < $end1)) {
        break;
      }
      $345 = *$b;
      switch ($345) {
        case 0:
          $347 = *($b + 1);
          if (($347 & 128) == 0) {
            continue;
          }
          break;
        case 255:
          $346 = *($b + 1);
          if (($346 & 128) != 0) {
            continue;
          }
          break;
        
      }
      break;
    }
    $size = $end - $b;
    if ($size > sizeof(long long)) {
      $343 = __errno_location();
      *$343 = 34;
      return -1;
    }
  }
  if ($end == $b) {
    *$lptr = 0;
    return 0;
  }
  $344 = asn__integer_convert($b, $end);
  *$lptr = $344;
  return 0;
}

int asn_INTEGER2umax(struct ASN__PRIMITIVE_TYPE_s *$iptr, unsigned long long *$lptr)
{
  register unsigned char *$b;
  register unsigned char *$end;
  register unsigned long long $value;
  register unsigned int $size;
  register int *$343;
  register int $342;
  register int $341;
  register int *$340;
  register unsigned char *$346;
  register unsigned char $345;
  register unsigned char $344;
  if (!$iptr) {
    $341 = 1;
  } else {
    $346 = (*$iptr).buf;
    $341 = (_Bool) !$346;
  }
  if ($341) {
    $342 = 1;
  } else {
    $342 = (_Bool) !$lptr;
  }
  if ($342) {
    $340 = __errno_location();
    *$340 = 22;
    return -1;
  }
  $b = (*$iptr).buf;
  $size = (*$iptr).size;
  $end = $b + $size;
  for (; 1; $b = $b + 1, $size = $size - 1) {
    if (! ($size > sizeof(unsigned long long))) {
      break;
    }
    $345 = *$b;
    if ($345) {
      $343 = __errno_location();
      *$343 = 34;
      return -1;
    }
  }
  $value = (unsigned long long) 0;
  for (; 1; $b = $b + 1) {
    if (! ($b < $end)) {
      break;
    }
    $344 = *$b;
    $value = $value << 8 | $344;
  }
  *$lptr = $value;
  return 0;
}

int asn_umax2INTEGER(struct ASN__PRIMITIVE_TYPE_s *$st, unsigned long long $value)
{
  register unsigned char *$buf;
  register unsigned char *$end;
  register unsigned char *$b;
  register int $shr;
  register void *$341;
  register int $340;
  register unsigned char *$343;
  register unsigned char *$342;
  if ($value <= ~((unsigned long long) 0) >> 1) {
    $340 = asn_imax2INTEGER($st, $value);
    return $340;
  }
  $341 = malloc(1 + sizeof(unsigned long long));
  $buf = (unsigned char *) $341;
  if (!$buf) {
    return -1;
  }
  $end = $buf + (sizeof(unsigned long long) + 1);
  *($buf + 0) = 0;
  $b = $buf + 1;
  $shr = (sizeof(unsigned long long) - 1) * 8;
  for (; 1; $shr = $shr - 8, $b = $b + 1) {
    if (! ($b < $end)) {
      break;
    }
    *$b = (unsigned char) ($value >> $shr);
  }
  $342 = (*$st).buf;
  if ($342) {
    $343 = (*$st).buf;
    free($343);
  }
  (*$st).buf = $buf;
  (*$st).size = 1 + sizeof(unsigned long long);
  return 0;
}

int asn_imax2INTEGER(struct ASN__PRIMITIVE_TYPE_s *$st, long long $value)
{
  long long value;
  int littleEndian;
  register unsigned char *$buf;
  register unsigned char *$bp;
  register unsigned char *$p;
  register unsigned char *$pstart;
  register unsigned char *$pend1;
  register int $add;
  register unsigned char *$342;
  register void *$341;
  register int *$340;
  register signed char $349;
  register unsigned char $348;
  register unsigned char $347;
  register unsigned char $346;
  register unsigned char $345;
  register unsigned char *$344;
  register unsigned char *$343;
  value = $value;
  littleEndian = 1;
  if (!$st) {
    $340 = __errno_location();
    *$340 = 22;
    return -1;
  }
  $341 = malloc(sizeof(long long));
  $buf = (unsigned char *) (int *) $341;
  if (!$buf) {
    return -1;
  }
  $349 = *((signed char *) &littleEndian);
  if ($349) {
    $pstart = (unsigned char *) &value + sizeof(long long) - 1;
    $pend1 = (unsigned char *) &value;
    $add = -1;
  } else {
    $pstart = (unsigned char *) &value;
    $pend1 = $pstart + sizeof(long long) - 1;
    $add = 1;
  }
  $p = $pstart;
  for (; 1; $p = $p + $add) {
    if (! ($p != $pend1)) {
      break;
    }
    $346 = *$p;
    switch ($346) {
      case 0:
        $348 = *($p + $add);
        if (($348 & 128) == 0) {
          continue;
        }
        break;
      case 255:
        $347 = *($p + $add);
        if ($347 & 128) {
          continue;
        }
        break;
      
    }
    break;
  }
  $bp = $buf;
  $pend1 = $pend1 + $add;
  for (; 1; $p = $p + $add) {
    if (! ($p != $pend1)) {
      break;
    }
    $342 = $bp;
    $bp = $342 + 1;
    $345 = *$p;
    *$342 = $345;
  }
  $343 = (*$st).buf;
  if ($343) {
    $344 = (*$st).buf;
    free($344);
  }
  (*$st).buf = $buf;
  (*$st).size = $bp - $buf;
  return 0;
}

int asn_INTEGER2long(struct ASN__PRIMITIVE_TYPE_s *$iptr, int *$l)
{
  long long v;
  register int $342;
  register int $341;
  register int *$340;
  register long long $345;
  register long long $344;
  register long long $343;
  $342 = asn_INTEGER2imax($iptr, &v);
  if ($342 == 0) {
    $344 = v;
    if ($344 < -2147483647 - 1) {
      $341 = 1;
    } else {
      $345 = v;
      $341 = (_Bool) ($345 > 2147483647);
    }
    if ($341) {
      $340 = __errno_location();
      *$340 = 34;
      return -1;
    }
    $343 = v;
    *$l = $343;
    return 0;
  } else {
    return -1;
  }
}

int asn_INTEGER2ulong(struct ASN__PRIMITIVE_TYPE_s *$iptr, unsigned int *$l)
{
  unsigned long long v;
  register int $341;
  register int *$340;
  register unsigned long long $343;
  register unsigned long long $342;
  $341 = asn_INTEGER2umax($iptr, &v);
  if ($341 == 0) {
    $343 = v;
    if ($343 > 2147483647 * 2U + 1U) {
      $340 = __errno_location();
      *$340 = 34;
      return -1;
    }
    $342 = v;
    *$l = $342;
    return 0;
  } else {
    return -1;
  }
}

int asn_long2INTEGER(struct ASN__PRIMITIVE_TYPE_s *$st, int $value)
{
  register int $340;
  $340 = asn_imax2INTEGER($st, $value);
  return $340;
}

int asn_ulong2INTEGER(struct ASN__PRIMITIVE_TYPE_s *$st, unsigned int $value)
{
  register int $340;
  $340 = asn_imax2INTEGER($st, $value);
  return $340;
}

int asn_strtoimax_lim(signed char *$str, signed char **$end, long long *$intp)
{
  register int $sign;
  register long long $value;
  register long long $asn1_intmax_max;
  register long long $upper_boundary;
  register long long $last_digit_max;
  register int $d;
  register int $341;
  register int $340;
  register signed char *$351;
  register signed char *$350;
  register signed char $349;
  register signed char *$348;
  register signed char $347;
  register signed char $346;
  register signed char $345;
  register signed char $344;
  register signed char $343;
  register signed char *$342;
  $sign = 1;
  $asn1_intmax_max = ~((unsigned long long) 0) >> 1;
  $upper_boundary = $asn1_intmax_max / 10;
  $last_digit_max = $asn1_intmax_max % 10;
  $351 = *$end;
  if ($str >= $351) {
    return -2;
  }
  $349 = *$str;
  switch ($349) {
    case 45:
      $last_digit_max = $last_digit_max + 1;
      $sign = -1;
    case 43:
      $str = $str + 1;
      $350 = *$end;
      if ($str >= $350) {
        *$end = $str;
        return -1;
      }
    
  }
  $value = (long long) 0;
  for (; 1; $str = $str + 1) {
    $348 = *$end;
    if (! ($str < $348)) {
      break;
    }
    $346 = *$str;
    if ($346 >= 48) {
      $347 = *$str;
      $341 = (_Bool) ($347 <= 57);
    } else {
      $341 = 0;
    }
    if ($341) {
      $345 = *$str;
      $d = $345 - 48;
      if ($value < $upper_boundary) {
        $value = $value * 10 + $d;
      } else {
        if ($value == $upper_boundary) {
          if ($d <= $last_digit_max) {
            if ($sign > 0) {
              $value = $value * 10 + $d;
            } else {
              $sign = 1;
              $value = -$value * 10 - $d;
            }
            $str = $str + 1;
            $342 = *$end;
            if ($str < $342) {
              *$end = $str;
              $343 = *$str;
              if ($343 >= 48) {
                $344 = *$str;
                $340 = (_Bool) ($344 <= 57);
              } else {
                $340 = 0;
              }
              if ($340) {
                return -3;
              } else {
                *$intp = $sign * $value;
                return 1;
              }
            }
            break;
          } else {
            *$end = $str;
            return -3;
          }
        } else {
          *$end = $str;
          return -3;
        }
      }
    } else {
      *$end = $str;
      *$intp = $sign * $value;
      return 1;
    }
  }
  *$end = $str;
  *$intp = $sign * $value;
  return 0;
}

int asn_strtoumax_lim(signed char *$str, signed char **$end, unsigned long long *$uintp)
{
  register unsigned long long $value;
  register unsigned long long $asn1_uintmax_max;
  register unsigned long long $upper_boundary;
  register unsigned long long $last_digit_max;
  register unsigned int $d;
  register int $341;
  register int $340;
  register signed char *$351;
  register signed char *$350;
  register signed char $349;
  register signed char *$348;
  register signed char $347;
  register signed char $346;
  register signed char $345;
  register signed char $344;
  register signed char $343;
  register signed char *$342;
  $asn1_uintmax_max = ~((unsigned long long) 0);
  $upper_boundary = $asn1_uintmax_max / 10;
  $last_digit_max = $asn1_uintmax_max % 10;
  $351 = *$end;
  if ($str >= $351) {
    return -2;
  }
  $349 = *$str;
  switch ($349) {
    case 45:
      return -2;
    case 43:
      $str = $str + 1;
      $350 = *$end;
      if ($str >= $350) {
        *$end = $str;
        return -1;
      }
    
  }
  $value = (unsigned long long) 0;
  for (; 1; $str = $str + 1) {
    $348 = *$end;
    if (! ($str < $348)) {
      break;
    }
    $346 = *$str;
    if ($346 >= 48) {
      $347 = *$str;
      $341 = (_Bool) ($347 <= 57);
    } else {
      $341 = 0;
    }
    if ($341) {
      $345 = *$str;
      $d = $345 - 48;
      if ($value < $upper_boundary) {
        $value = $value * 10 + $d;
      } else {
        if ($value == $upper_boundary) {
          if ($d <= $last_digit_max) {
            $value = $value * 10 + $d;
            $str = $str + 1;
            $342 = *$end;
            if ($str < $342) {
              *$end = $str;
              $343 = *$str;
              if ($343 >= 48) {
                $344 = *$str;
                $340 = (_Bool) ($344 <= 57);
              } else {
                $340 = 0;
              }
              if ($340) {
                return -3;
              } else {
                *$uintp = $value;
                return 1;
              }
            }
            break;
          } else {
            *$end = $str;
            return -3;
          }
        } else {
          *$end = $str;
          return -3;
        }
      }
    } else {
      *$end = $str;
      *$uintp = $value;
      return 1;
    }
  }
  *$end = $str;
  *$uintp = $value;
  return 0;
}

signed char const __func__[15] = { 97, 115, 110, 95, 115, 116, 114, 116, 111,
  108, 95, 108, 105, 109, 0, };

int asn_strtol_lim(signed char *$str, signed char **$end, int *$lp)
{
  long long value;
  register int $342;
  register int $341;
  register int $340;
  register long long $348;
  register long long $347;
  register long long $346;
  register long long $345;
  register long long $344;
  register long long $343;
  $340 = asn_strtoimax_lim($str, $end, &value);
  switch ($340) {
    case 4294967293:
      return -3;
    case 4294967294:
      return -2;
    case 4294967295:
      return -1;
    case 0:
      $347 = value;
      if ($347 >= -2147483647 - 1) {
        $348 = value;
        $341 = (_Bool) ($348 <= 2147483647);
      } else {
        $341 = 0;
      }
      if ($341) {
        $346 = value;
        *$lp = $346;
        return 0;
      } else {
        return -3;
      }
    case 1:
      $344 = value;
      if ($344 >= -2147483647 - 1) {
        $345 = value;
        $342 = (_Bool) ($345 <= 2147483647);
      } else {
        $342 = 0;
      }
      if ($342) {
        $343 = value;
        *$lp = $343;
        return 1;
      } else {
        return -3;
      }
    
  }
  if (! !__stringlit_10) {
    __assert_fail(__stringlit_9, __stringlit_8, 1195, __func__);
  }
  return -2;
}

signed char const __func____1[16] = { 97, 115, 110, 95, 115, 116, 114, 116,
  111, 117, 108, 95, 108, 105, 109, 0, };

int asn_strtoul_lim(signed char *$str, signed char **$end, unsigned int *$ulp)
{
  unsigned long long value;
  register int $340;
  register unsigned long long $344;
  register unsigned long long $343;
  register unsigned long long $342;
  register unsigned long long $341;
  $340 = asn_strtoumax_lim($str, $end, &value);
  switch ($340) {
    case 4294967293:
      return -3;
    case 4294967294:
      return -2;
    case 4294967295:
      return -1;
    case 0:
      $343 = value;
      if ($343 <= 2147483647 * 2U + 1U) {
        $344 = value;
        *$ulp = $344;
        return 0;
      } else {
        return -3;
      }
    case 1:
      $341 = value;
      if ($341 <= 2147483647 * 2U + 1U) {
        $342 = value;
        *$ulp = $342;
        return 1;
      } else {
        return -3;
      }
    
  }
  if (! !__stringlit_10) {
    __assert_fail(__stringlit_9, __stringlit_8, 1225, __func____1);
  }
  return -2;
}

int INTEGER_compare(struct asn_TYPE_descriptor_s *$td, void *$aptr, void *$bptr)
{
  register struct ASN__PRIMITIVE_TYPE_s *$a;
  register struct ASN__PRIMITIVE_TYPE_s *$b;
  register int $sign_a;
  register int $sign_b;
  register int $sign;
  register int $sign__1;
  register int $347;
  register int $346;
  register int $345;
  register int $344;
  register int $343;
  register int $342;
  register int $341;
  register int $340;
  register unsigned int $366;
  register unsigned int $365;
  register unsigned char $364;
  register unsigned char *$363;
  register unsigned char $362;
  register unsigned char *$361;
  register unsigned int $360;
  register unsigned int $359;
  register unsigned int $358;
  register unsigned int $357;
  register unsigned int $356;
  register unsigned char *$355;
  register unsigned char *$354;
  register unsigned char $353;
  register unsigned char *$352;
  register unsigned char $351;
  register unsigned char *$350;
  register unsigned int $349;
  register unsigned int $348;
  $a = $aptr;
  $b = $bptr;
  if ($a) {
    $347 = (_Bool) $b;
  } else {
    $347 = 0;
  }
  if ($347) {
    $365 = (*$a).size;
    if ($365) {
      $366 = (*$b).size;
      $345 = (_Bool) $366;
    } else {
      $345 = 0;
    }
    if ($345) {
      $363 = (*$a).buf;
      $364 = *($363 + 0);
      if ($364 & 128) {
        $340 = (int) -1;
      } else {
        $340 = (int) 1;
      }
      $sign_a = $340;
      $361 = (*$b).buf;
      $362 = *($361 + 0);
      if ($362 & 128) {
        $341 = (int) -1;
      } else {
        $341 = (int) 1;
      }
      $sign_b = $341;
      if ($sign_a < $sign_b) {
        return -1;
      }
      if ($sign_a > $sign_b) {
        return 1;
      }
      $357 = (*$a).size;
      $358 = (*$b).size;
      if ($357 < $358) {
        return -1 * $sign_a;
      } else {
        $359 = (*$a).size;
        $360 = (*$b).size;
        if ($359 > $360) {
          return 1 * $sign_b;
        }
      }
      $354 = (*$a).buf;
      $355 = (*$b).buf;
      $356 = (*$a).size;
      $342 = memcmp($354, $355, $356);
      return $sign_a * $342;
    } else {
      $348 = (*$a).size;
      if ($348) {
        $352 = (*$a).buf;
        $353 = *($352 + 0);
        if ($353 & 128) {
          $343 = (int) -1;
        } else {
          $343 = (int) 1;
        }
        $sign = $343;
        return 1 * $sign;
      } else {
        $349 = (*$b).size;
        if ($349) {
          $350 = (*$a).buf;
          $351 = *($350 + 0);
          if ($351 & 128) {
            $344 = (int) -1;
          } else {
            $344 = (int) 1;
          }
          $sign__1 = $344;
          return -1 * $sign__1;
        } else {
          return 0;
        }
      }
    }
  } else {
    if (!$a) {
      $346 = (_Bool) !$b;
    } else {
      $346 = 0;
    }
    if ($346) {
      return 0;
    } else {
      if (!$a) {
        return -1;
      } else {
        return 1;
      }
    }
  }
}

signed char const __func____2[20] = { 73, 78, 84, 69, 71, 69, 82, 95, 114,
  97, 110, 100, 111, 109, 95, 102, 105, 108, 108, 0, };

int const variants[38] = { -65536, -65535, -65534, -32769, -32768, -32767,
  -16385, -16384, -16383, -257, -256, -255, -254, -129, -128, -127, -126, -1,
  0, 1, 126, 127, 128, 129, 254, 255, 256, 257, 16383, 16384, 16385, 32767,
  32768, 32769, 65534, 65535, 65536, 65537, };

void INTEGER_random_fill(struct asn_random_fill_result_s *$_res, struct asn_TYPE_descriptor_s *$td, void **$sptr, struct asn_encoding_constraints_s *$constraints, unsigned int $max_length)
{
  struct asn_random_fill_result_s result_ok;
  struct asn_random_fill_result_s result_failed;
  struct asn_random_fill_result_s result_skipped;
  register struct asn_INTEGER_specifics_s *$specs;
  register struct ASN__PRIMITIVE_TYPE_s *$st;
  register struct asn_INTEGER_enum_map_s *$emap;
  register unsigned int $emap_len;
  register long long $value;
  register int $find_inside_map;
  register struct asn_per_constraints_s *$ct;
  register int $351;
  register int $350;
  register int $349;
  register long long $348;
  register void *$347;
  register int $346;
  register long long $345;
  register long long $344;
  register long long $343;
  register long long $342;
  register long long $341;
  register void *$340;
  register void *$370;
  register int $369;
  register int $368;
  register int $367;
  register int $366;
  register int $365;
  register int $364;
  register struct asn_per_constraints_s *$363;
  register int $362;
  register int $361;
  register int $360;
  register int $359;
  register int $358;
  register void (*$357)(struct asn_TYPE_descriptor_s *, void *, int);
  register struct asn_TYPE_operation_s *$356;
  register void (*$355)(struct asn_TYPE_descriptor_s *, void *, int);
  register struct asn_TYPE_operation_s *$354;
  register void *$353;
  register unsigned int $352;
  $370 = (*$td).specifics;
  $specs = (struct asn_INTEGER_specifics_s *) $370;
  result_ok.code = 0;
  result_ok.length = 1;
  result_failed.code = -1;
  result_failed.length = 0;
  result_skipped.code = 1;
  result_skipped.length = 0;
  $st = *$sptr;
  if ($max_length == 0) {
    *$_res = result_skipped;
    return;
  }
  if ($st == (void *) 0) {
    $340 = calloc(1, sizeof(struct ASN__PRIMITIVE_TYPE_s));
    $st = (struct ASN__PRIMITIVE_TYPE_s *) $340;
    if ($st == (void *) 0) {
      *$_res = result_failed;
      return;
    }
  }
  if ($specs) {
    $emap = (*$specs).value2enum;
    $emap_len = (*$specs).map_count;
    $369 = (*$specs).strict_enumeration;
    if ($369) {
      $find_inside_map = $emap_len > 0;
    } else {
      if ($emap_len) {
        $342 = asn_random_between(0, 1);
        $341 = (long long) $342;
      } else {
        $341 = (long long) 0;
      }
      $find_inside_map = (int) $341;
    }
  } else {
    $emap = 0;
    $emap_len = 0;
    $find_inside_map = 0;
  }
  if ($find_inside_map) {
    if (! ($emap_len > 0)) {
      __assert_fail(__stringlit_12, __stringlit_8, 1311, __func____2);
    }
    $343 = asn_random_between(0, $emap_len - 1);
    $368 = (*($emap + $343)).nat_value;
    $value = (long long) $368;
  } else {
    if ($specs) {
      $367 = (*$specs).field_unsigned;
      $346 = (_Bool) $367;
    } else {
      $346 = 0;
    }
    if ($346) {
      $366 = *(variants + 18);
      if (! ($366 == 0)) {
        __assert_fail(__stringlit_11, __stringlit_8, 1323, __func____2);
      }
      $344 = asn_random_between(18, sizeof(int [38]) / sizeof(int) - 1);
      $365 = *(variants + $344);
      $value = (long long) $365;
    } else {
      $345 = asn_random_between(0, sizeof(int [38]) / sizeof(int) - 1);
      $364 = *(variants + $345);
      $value = (long long) $364;
    }
    if (!$constraints) {
      $constraints = &(*$td).encoding_constraints;
    }
    if ($constraints) {
      $363 = (*$constraints).per_constraints;
      $347 = (void *) $363;
    } else {
      $347 = (void *) (void *) 0;
    }
    $ct = $347;
    if ($ct) {
      $362 = (*$ct).value.flags;
      $350 = (_Bool) ($362 & 2);
    } else {
      $350 = 0;
    }
    if ($350) {
      $360 = (*$ct).value.lower_bound;
      if ($value < $360) {
        $349 = 1;
      } else {
        $361 = (*$ct).value.upper_bound;
        $349 = (_Bool) ($value > $361);
      }
      if ($349) {
        $358 = (*$ct).value.lower_bound;
        $359 = (*$ct).value.upper_bound;
        $348 = asn_random_between($358, $359);
        $value = $348;
      }
    }
  }
  $351 = asn_imax2INTEGER($st, $value);
  if ($351) {
    $353 = *$sptr;
    if ($st == $353) {
      $356 = (*$td).op;
      $357 = (*$356).free_struct;
      $357($td, $st, 2);
    } else {
      $354 = (*$td).op;
      $355 = (*$354).free_struct;
      $355($td, $st, 0);
    }
    *$_res = result_failed;
    return;
  } else {
    *$sptr = $st;
    $352 = (*$st).size;
    result_ok.length = $352;
    *$_res = result_ok;
    return;
  }
}


