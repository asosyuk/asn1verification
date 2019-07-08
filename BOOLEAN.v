From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.4"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "/home/nika/asn1c/skeletons/BOOLEAN.c"%string.
  Definition normalized := true.
End Info.

Definition _ASN__PRIMITIVE_TYPE_free : ident := 154%positive.
Definition _BOOLEAN__xer_body_decode : ident := 192%positive.
Definition _BOOLEAN_compare : ident := 169%positive.
Definition _BOOLEAN_decode_ber : ident := 168%positive.
Definition _BOOLEAN_decode_oer : ident := 164%positive.
Definition _BOOLEAN_decode_uper : ident := 162%positive.
Definition _BOOLEAN_decode_xer : ident := 166%positive.
Definition _BOOLEAN_encode_der : ident := 167%positive.
Definition _BOOLEAN_encode_oer : ident := 163%positive.
Definition _BOOLEAN_encode_uper : ident := 161%positive.
Definition _BOOLEAN_encode_xer : ident := 165%positive.
Definition _BOOLEAN_free : ident := 171%positive.
Definition _BOOLEAN_print : ident := 170%positive.
Definition _BOOLEAN_random_fill : ident := 160%positive.
Definition ___builtin_ais_annot : ident := 87%positive.
Definition ___builtin_annot : ident := 94%positive.
Definition ___builtin_annot_intval : ident := 95%positive.
Definition ___builtin_bswap : ident := 88%positive.
Definition ___builtin_bswap16 : ident := 90%positive.
Definition ___builtin_bswap32 : ident := 89%positive.
Definition ___builtin_bswap64 : ident := 120%positive.
Definition ___builtin_clz : ident := 121%positive.
Definition ___builtin_clzl : ident := 122%positive.
Definition ___builtin_clzll : ident := 123%positive.
Definition ___builtin_ctz : ident := 124%positive.
Definition ___builtin_ctzl : ident := 125%positive.
Definition ___builtin_ctzll : ident := 126%positive.
Definition ___builtin_debug : ident := 138%positive.
Definition ___builtin_fabs : ident := 91%positive.
Definition ___builtin_fmadd : ident := 129%positive.
Definition ___builtin_fmax : ident := 127%positive.
Definition ___builtin_fmin : ident := 128%positive.
Definition ___builtin_fmsub : ident := 130%positive.
Definition ___builtin_fnmadd : ident := 131%positive.
Definition ___builtin_fnmsub : ident := 132%positive.
Definition ___builtin_fsqrt : ident := 92%positive.
Definition ___builtin_membar : ident := 96%positive.
Definition ___builtin_memcpy_aligned : ident := 93%positive.
Definition ___builtin_nop : ident := 137%positive.
Definition ___builtin_read16_reversed : ident := 133%positive.
Definition ___builtin_read32_reversed : ident := 134%positive.
Definition ___builtin_va_arg : ident := 98%positive.
Definition ___builtin_va_copy : ident := 99%positive.
Definition ___builtin_va_end : ident := 100%positive.
Definition ___builtin_va_start : ident := 97%positive.
Definition ___builtin_write16_reversed : ident := 135%positive.
Definition ___builtin_write32_reversed : ident := 136%positive.
Definition ___compcert_i64_dtos : ident := 105%positive.
Definition ___compcert_i64_dtou : ident := 106%positive.
Definition ___compcert_i64_sar : ident := 117%positive.
Definition ___compcert_i64_sdiv : ident := 111%positive.
Definition ___compcert_i64_shl : ident := 115%positive.
Definition ___compcert_i64_shr : ident := 116%positive.
Definition ___compcert_i64_smod : ident := 113%positive.
Definition ___compcert_i64_smulh : ident := 118%positive.
Definition ___compcert_i64_stod : ident := 107%positive.
Definition ___compcert_i64_stof : ident := 109%positive.
Definition ___compcert_i64_udiv : ident := 112%positive.
Definition ___compcert_i64_umod : ident := 114%positive.
Definition ___compcert_i64_umulh : ident := 119%positive.
Definition ___compcert_i64_utod : ident := 108%positive.
Definition ___compcert_i64_utof : ident := 110%positive.
Definition ___compcert_va_composite : ident := 104%positive.
Definition ___compcert_va_float64 : ident := 103%positive.
Definition ___compcert_va_int32 : ident := 101%positive.
Definition ___compcert_va_int64 : ident := 102%positive.
Definition ___stringlit_1 : ident := 173%positive.
Definition ___stringlit_2 : ident := 190%positive.
Definition ___stringlit_3 : ident := 191%positive.
Definition ___stringlit_4 : ident := 198%positive.
Definition ___stringlit_5 : ident := 200%positive.
Definition ___stringlit_6 : ident := 203%positive.
Definition ___stringlit_7 : ident := 204%positive.
Definition ___stringlit_8 : ident := 205%positive.
Definition __res : ident := 174%positive.
Definition __res__1 : ident := 182%positive.
Definition _a : ident := 214%positive.
Definition _all_tags : ident := 72%positive.
Definition _all_tags_count : ident := 73%positive.
Definition _app_key : ident := 185%positive.
Definition _aptr : ident := 212%positive.
Definition _asn_DEF_BOOLEAN : ident := 172%positive.
Definition _asn_DEF_BOOLEAN_tags : ident := 158%positive.
Definition _asn_OP_BOOLEAN : ident := 159%positive.
Definition _asn_TYPE_descriptor_s : ident := 4%positive.
Definition _asn_TYPE_member_s : ident := 75%positive.
Definition _asn_TYPE_operation_s : ident := 63%positive.
Definition _asn_TYPE_outmost_tag : ident := 153%positive.
Definition _asn_bit_data_s : ident := 21%positive.
Definition _asn_bit_outp_s : ident := 28%positive.
Definition _asn_codec_ctx_s : ident := 2%positive.
Definition _asn_dec_rval_s : ident := 10%positive.
Definition _asn_enc_rval_s : ident := 7%positive.
Definition _asn_encoding_constraints_s : ident := 60%positive.
Definition _asn_generic_no_constraint : ident := 148%positive.
Definition _asn_generic_unknown_constraint : ident := 149%positive.
Definition _asn_get_few_bits : ident := 146%positive.
Definition _asn_oer_constraint_number_s : ident := 44%positive.
Definition _asn_oer_constraints_s : ident := 45%positive.
Definition _asn_per_constraint_s : ident := 34%positive.
Definition _asn_per_constraints_s : ident := 39%positive.
Definition _asn_put_few_bits : ident := 147%positive.
Definition _asn_random_between : ident := 150%positive.
Definition _asn_random_fill_result_s : ident := 41%positive.
Definition _asn_struct_ctx_s : ident := 16%positive.
Definition _asn_type_selector_result_s : ident := 48%positive.
Definition _b : ident := 215%positive.
Definition _ber_check_tags : ident := 143%positive.
Definition _ber_decode_primitive : ident := 155%positive.
Definition _ber_decoder : ident := 52%positive.
Definition _bool_value : ident := 177%positive.
Definition _bptr : ident := 213%positive.
Definition _buf : ident := 201%positive.
Definition _buf_ptr : ident := 178%positive.
Definition _buffer : ident := 17%positive.
Definition _buflen : ident := 202%positive.
Definition _calloc : ident := 140%positive.
Definition _cb : ident := 184%positive.
Definition _cb_failed : ident := 199%positive.
Definition _chunk_buf : ident := 187%positive.
Definition _chunk_size : ident := 188%positive.
Definition _code : ident := 8%positive.
Definition _code2value : ident := 38%positive.
Definition _compare_struct : ident := 51%positive.
Definition _constraints : ident := 207%positive.
Definition _consumed : ident := 9%positive.
Definition _context : ident := 13%positive.
Definition _default_value_cmp : ident := 85%positive.
Definition _default_value_set : ident := 86%positive.
Definition _der_encode_primitive : ident := 156%positive.
Definition _der_encoder : ident := 53%positive.
Definition _der_write_tags : ident := 144%positive.
Definition _effective_bits : ident := 31%positive.
Definition _elements : ident := 76%positive.
Definition _elements_count : ident := 77%positive.
Definition _encoded : ident := 3%positive.
Definition _encoding_constraints : ident := 74%positive.
Definition _er : ident := 195%positive.
Definition _erval : ident := 186%positive.
Definition _failed_type : ident := 5%positive.
Definition _flags : ident := 29%positive.
Definition _flushed_bytes : ident := 27%positive.
Definition _free : ident := 141%positive.
Definition _free_struct : ident := 49%positive.
Definition _general_constraints : ident := 66%positive.
Definition _ilevel : ident := 194%positive.
Definition _left : ident := 15%positive.
Definition _length : ident := 40%positive.
Definition _lidx : ident := 181%positive.
Definition _lower_bound : ident := 32%positive.
Definition _main : ident := 221%positive.
Definition _malloc : ident := 139%positive.
Definition _max_length : ident := 216%positive.
Definition _max_stack_size : ident := 1%positive.
Definition _memb_offset : ident := 80%positive.
Definition _memset : ident := 142%positive.
Definition _method : ident := 206%positive.
Definition _moved : ident := 20%positive.
Definition _name : ident := 67%positive.
Definition _nbits : ident := 19%positive.
Definition _nboff : ident := 18%positive.
Definition _oer_constraints : ident := 64%positive.
Definition _oer_decode_primitive : ident := 151%positive.
Definition _oer_decoder : ident := 56%positive.
Definition _oer_encode_primitive : ident := 152%positive.
Definition _oer_encoder : ident := 57%positive.
Definition _ok : ident := 211%positive.
Definition _op : ident := 69%positive.
Definition _op_key : ident := 26%positive.
Definition _opt_codec_ctx : ident := 175%positive.
Definition _opt_mname : ident := 193%positive.
Definition _optional : ident := 79%positive.
Definition _outmost_tag : ident := 62%positive.
Definition _output : ident := 25%positive.
Definition _p : ident := 189%positive.
Definition _pc : ident := 220%positive.
Definition _pd : ident := 208%positive.
Definition _per_constraints : ident := 65%positive.
Definition _phase : ident := 11%positive.
Definition _po : ident := 210%positive.
Definition _positive : ident := 43%positive.
Definition _presence_index : ident := 47%positive.
Definition _print_struct : ident := 50%positive.
Definition _ptr : ident := 14%positive.
Definition _random_fill : ident := 61%positive.
Definition _range_bits : ident := 30%positive.
Definition _refill : ident := 22%positive.
Definition _refill_key : ident := 23%positive.
Definition _result_failed : ident := 218%positive.
Definition _result_ok : ident := 217%positive.
Definition _result_skipped : ident := 219%positive.
Definition _rv : ident := 209%positive.
Definition _rval : ident := 180%positive.
Definition _size : ident := 36%positive.
Definition _specifics : ident := 78%positive.
Definition _sptr : ident := 183%positive.
Definition _st : ident := 179%positive.
Definition _step : ident := 12%positive.
Definition _structure_ptr : ident := 6%positive.
Definition _tag : ident := 81%positive.
Definition _tag_mode : ident := 82%positive.
Definition _tags : ident := 70%positive.
Definition _tags_count : ident := 71%positive.
Definition _td : ident := 176%positive.
Definition _tmp_error : ident := 196%positive.
Definition _tmp_error__1 : ident := 197%positive.
Definition _tmpspace : ident := 24%positive.
Definition _type : ident := 83%positive.
Definition _type_descriptor : ident := 46%positive.
Definition _type_selector : ident := 84%positive.
Definition _uper_decoder : ident := 58%positive.
Definition _uper_encoder : ident := 59%positive.
Definition _upper_bound : ident := 33%positive.
Definition _value : ident := 35%positive.
Definition _value2code : ident := 37%positive.
Definition _width : ident := 42%positive.
Definition _xer_check_tag : ident := 145%positive.
Definition _xer_decode_primitive : ident := 157%positive.
Definition _xer_decoder : ident := 54%positive.
Definition _xer_encoder : ident := 55%positive.
Definition _xml_tag : ident := 68%positive.
Definition _t'1 : ident := 222%positive.
Definition _t'10 : ident := 231%positive.
Definition _t'11 : ident := 232%positive.
Definition _t'12 : ident := 233%positive.
Definition _t'13 : ident := 234%positive.
Definition _t'14 : ident := 235%positive.
Definition _t'2 : ident := 223%positive.
Definition _t'3 : ident := 224%positive.
Definition _t'4 : ident := 225%positive.
Definition _t'5 : ident := 226%positive.
Definition _t'6 : ident := 227%positive.
Definition _t'7 : ident := 228%positive.
Definition _t'8 : ident := 229%positive.
Definition _t'9 : ident := 230%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 79) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_asn_DEF_BOOLEAN_tags := {|
  gvar_info := (tarray tuint 1);
  gvar_init := (Init_int32 (Int.repr 4) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_asn_OP_BOOLEAN := {|
  gvar_info := (Tstruct _asn_TYPE_operation_s noattr);
  gvar_init := (Init_addrof _BOOLEAN_free (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_print (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_compare (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_decode_ber (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_encode_der (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_decode_xer (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_encode_xer (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_decode_oer (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_encode_oer (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_decode_uper (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_encode_uper (Ptrofs.repr 0) ::
                Init_addrof _BOOLEAN_random_fill (Ptrofs.repr 0) ::
                Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_asn_DEF_BOOLEAN := {|
  gvar_info := (Tstruct _asn_TYPE_descriptor_s noattr);
  gvar_init := (Init_addrof ___stringlit_1 (Ptrofs.repr 0) ::
                Init_addrof ___stringlit_1 (Ptrofs.repr 0) ::
                Init_addrof _asn_OP_BOOLEAN (Ptrofs.repr 0) ::
                Init_addrof _asn_DEF_BOOLEAN_tags (Ptrofs.repr 0) ::
                Init_int32 (Int.repr 1) ::
                Init_addrof _asn_DEF_BOOLEAN_tags (Ptrofs.repr 0) ::
                Init_int32 (Int.repr 1) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) ::
                Init_addrof _asn_generic_no_constraint (Ptrofs.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_BOOLEAN_decode_ber := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_dec_rval_s noattr))) ::
                (_opt_codec_ctx, (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_bool_value, (tptr (tptr tvoid))) ::
                (_buf_ptr, (tptr tvoid)) :: (_size, tuint) ::
                (_tag_mode, tint) :: nil);
  fn_vars := ((_rval, (Tstruct _asn_dec_rval_s noattr)) :: (_length, tint) ::
              (__res__1, (Tstruct _asn_dec_rval_s noattr)) :: nil);
  fn_temps := ((_st, (tptr tint)) :: (_lidx, tint) :: (_t'3, tint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'14, (tptr tvoid)) :: (_t'13, tint) :: (_t'12, tuint) ::
               (_t'11, tuint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, tuchar) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'14
      (Ederef (Etempvar _bool_value (tptr (tptr tvoid))) (tptr tvoid)))
    (Sset _st (Ecast (Etempvar _t'14 (tptr tvoid)) (tptr tint))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _st (tptr tint))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _calloc (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                (tptr tvoid) cc_default))
                ((Econst_int (Int.repr 1) tint) :: (Esizeof tint tuint) ::
                 nil))
              (Sset _t'2 (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tvoid))))
            (Sassign
              (Ederef (Etempvar _bool_value (tptr (tptr tvoid)))
                (tptr tvoid)) (Etempvar _t'2 (tptr tvoid))))
          (Sset _st (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tint))))
        (Sifthenelse (Ebinop Oeq (Etempvar _st (tptr tint))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Sassign
              (Efield (Evar _rval (Tstruct _asn_dec_rval_s noattr)) _code
                tint) (Econst_int (Int.repr 2) tint))
            (Ssequence
              (Sassign
                (Efield (Evar _rval (Tstruct _asn_dec_rval_s noattr))
                  _consumed tuint) (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                    (Tstruct _asn_dec_rval_s noattr))
                  (Evar _rval (Tstruct _asn_dec_rval_s noattr)))
                (Sreturn None))))
          Sskip))
      Sskip)
    (Ssequence
      (Sloop Sskip Sbreak)
      (Ssequence
        (Ssequence
          (Scall None
            (Evar _ber_check_tags (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _asn_dec_rval_s noattr))
                                      (Tcons
                                        (tptr (Tstruct _asn_codec_ctx_s noattr))
                                        (Tcons
                                          (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                          (Tcons
                                            (tptr (Tstruct _asn_struct_ctx_s noattr))
                                            (Tcons (tptr tvoid)
                                              (Tcons tuint
                                                (Tcons tint
                                                  (Tcons tint
                                                    (Tcons (tptr tint)
                                                      (Tcons (tptr tint)
                                                        Tnil)))))))))) tvoid
                                    {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
            ((Eaddrof (Evar __res__1 (Tstruct _asn_dec_rval_s noattr))
               (tptr (Tstruct _asn_dec_rval_s noattr))) ::
             (Etempvar _opt_codec_ctx (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
             (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
             (Econst_int (Int.repr 0) tint) ::
             (Etempvar _buf_ptr (tptr tvoid)) :: (Etempvar _size tuint) ::
             (Etempvar _tag_mode tint) :: (Econst_int (Int.repr 0) tint) ::
             (Eaddrof (Evar _length tint) (tptr tint)) ::
             (Econst_int (Int.repr 0) tint) :: nil))
          (Sassign (Evar _rval (Tstruct _asn_dec_rval_s noattr))
            (Evar __res__1 (Tstruct _asn_dec_rval_s noattr))))
        (Ssequence
          (Ssequence
            (Sset _t'13
              (Efield (Evar _rval (Tstruct _asn_dec_rval_s noattr)) _code
                tint))
            (Sifthenelse (Ebinop One (Etempvar _t'13 tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Sassign
                  (Ederef
                    (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                    (Tstruct _asn_dec_rval_s noattr))
                  (Evar _rval (Tstruct _asn_dec_rval_s noattr)))
                (Sreturn None))
              Sskip))
          (Ssequence
            (Sloop Sskip Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'12
                  (Efield (Evar _rval (Tstruct _asn_dec_rval_s noattr))
                    _consumed tuint))
                (Sset _buf_ptr
                  (Ebinop Oadd
                    (Ecast (Etempvar _buf_ptr (tptr tvoid)) (tptr tschar))
                    (Etempvar _t'12 tuint) (tptr tschar))))
              (Ssequence
                (Ssequence
                  (Sset _t'11
                    (Efield (Evar _rval (Tstruct _asn_dec_rval_s noattr))
                      _consumed tuint))
                  (Sset _size
                    (Ebinop Osub (Etempvar _size tuint)
                      (Etempvar _t'11 tuint) tuint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'10 (Evar _length tint))
                    (Sifthenelse (Ebinop Ogt (Etempvar _t'10 tint)
                                   (Ecast (Etempvar _size tuint) tint) tint)
                      (Ssequence
                        (Sassign
                          (Efield
                            (Evar _rval (Tstruct _asn_dec_rval_s noattr))
                            _code tint) (Econst_int (Int.repr 1) tint))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Evar _rval (Tstruct _asn_dec_rval_s noattr))
                              _consumed tuint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                                (Tstruct _asn_dec_rval_s noattr))
                              (Evar _rval (Tstruct _asn_dec_rval_s noattr)))
                            (Sreturn None))))
                      Sskip))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sassign (Ederef (Etempvar _st (tptr tint)) tint)
                          (Econst_int (Int.repr 0) tint))
                        (Sset _lidx (Econst_int (Int.repr 0) tint)))
                      (Sloop
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'8 (Evar _length tint))
                              (Sifthenelse (Ebinop Olt (Etempvar _lidx tint)
                                             (Etempvar _t'8 tint) tint)
                                (Ssequence
                                  (Sset _t'9
                                    (Ederef (Etempvar _st (tptr tint)) tint))
                                  (Sset _t'3
                                    (Ecast
                                      (Ebinop Oeq (Etempvar _t'9 tint)
                                        (Econst_int (Int.repr 0) tint) tint)
                                      tbool)))
                                (Sset _t'3 (Econst_int (Int.repr 0) tint))))
                            (Sifthenelse (Etempvar _t'3 tint) Sskip Sbreak))
                          (Ssequence
                            (Sset _t'6
                              (Ederef (Etempvar _st (tptr tint)) tint))
                            (Ssequence
                              (Sset _t'7
                                (Ederef
                                  (Ebinop Oadd
                                    (Ecast (Etempvar _buf_ptr (tptr tvoid))
                                      (tptr tuchar)) (Etempvar _lidx tint)
                                    (tptr tuchar)) tuchar))
                              (Sassign
                                (Ederef (Etempvar _st (tptr tint)) tint)
                                (Ebinop Oor (Etempvar _t'6 tint)
                                  (Etempvar _t'7 tuchar) tint)))))
                        (Sset _lidx
                          (Ebinop Oadd (Etempvar _lidx tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Ssequence
                      (Sassign
                        (Efield (Evar _rval (Tstruct _asn_dec_rval_s noattr))
                          _code tint) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Ssequence
                          (Sset _t'4
                            (Efield
                              (Evar _rval (Tstruct _asn_dec_rval_s noattr))
                              _consumed tuint))
                          (Ssequence
                            (Sset _t'5 (Evar _length tint))
                            (Sassign
                              (Efield
                                (Evar _rval (Tstruct _asn_dec_rval_s noattr))
                                _consumed tuint)
                              (Ebinop Oadd (Etempvar _t'4 tuint)
                                (Etempvar _t'5 tint) tuint))))
                        (Ssequence
                          (Sloop Sskip Sbreak)
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                                (Tstruct _asn_dec_rval_s noattr))
                              (Evar _rval (Tstruct _asn_dec_rval_s noattr)))
                            (Sreturn None)))))))))))))))
|}.

Definition f_BOOLEAN_encode_der := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_enc_rval_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr tvoid)) :: (_tag_mode, tint) ::
                (_tag, tuint) ::
                (_cb,
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                         cc_default))) :: (_app_key, (tptr tvoid)) :: nil);
  fn_vars := ((_erval, (Tstruct _asn_enc_rval_s noattr)) ::
              (_bool_value, tuchar) :: nil);
  fn_temps := ((_st, (tptr tint)) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _st (Ecast (Etempvar _sptr (tptr tvoid)) (tptr tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _der_write_tags (Tfunction
                                (Tcons
                                  (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                  (Tcons tuint
                                    (Tcons tint
                                      (Tcons tint
                                        (Tcons tuint
                                          (Tcons
                                            (tptr (Tfunction
                                                    (Tcons (tptr tvoid)
                                                      (Tcons tuint
                                                        (Tcons (tptr tvoid)
                                                          Tnil))) tint
                                                    cc_default))
                                            (Tcons (tptr tvoid) Tnil)))))))
                                tint cc_default))
        ((Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
         (Econst_int (Int.repr 1) tint) :: (Etempvar _tag_mode tint) ::
         (Econst_int (Int.repr 0) tint) :: (Etempvar _tag tuint) ::
         (Etempvar _cb (tptr (Tfunction
                               (Tcons (tptr tvoid)
                                 (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                               tint cc_default))) ::
         (Etempvar _app_key (tptr tvoid)) :: nil))
      (Sassign
        (Efield (Evar _erval (Tstruct _asn_enc_rval_s noattr)) _encoded tint)
        (Etempvar _t'1 tint)))
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield (Evar _erval (Tstruct _asn_enc_rval_s noattr)) _encoded
            tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tint)
                       (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint)
          (Ssequence
            (Sassign
              (Efield (Evar _erval (Tstruct _asn_enc_rval_s noattr))
                _failed_type (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
              (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
            (Ssequence
              (Sassign
                (Efield (Evar _erval (Tstruct _asn_enc_rval_s noattr))
                  _structure_ptr (tptr tvoid)) (Etempvar _sptr (tptr tvoid)))
              (Ssequence
                (Sassign
                  (Ederef
                    (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                    (Tstruct _asn_enc_rval_s noattr))
                  (Evar _erval (Tstruct _asn_enc_rval_s noattr)))
                (Sreturn None))))
          Sskip))
      (Ssequence
        (Sifthenelse (Etempvar _cb (tptr (Tfunction
                                           (Tcons (tptr tvoid)
                                             (Tcons tuint
                                               (Tcons (tptr tvoid) Tnil)))
                                           tint cc_default)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'5 (Ederef (Etempvar _st (tptr tint)) tint))
                (Sifthenelse (Etempvar _t'5 tint)
                  (Sset _t'2 (Ecast (Econst_int (Int.repr 255) tint) tint))
                  (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tint))))
              (Sassign (Evar _bool_value tuchar) (Etempvar _t'2 tint)))
            (Ssequence
              (Scall (Some _t'3)
                (Etempvar _cb (tptr (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons tuint
                                          (Tcons (tptr tvoid) Tnil))) tint
                                      cc_default)))
                ((Eaddrof (Evar _bool_value tuchar) (tptr tuchar)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Etempvar _app_key (tptr tvoid)) :: nil))
              (Sifthenelse (Ebinop Olt (Etempvar _t'3 tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Sassign
                    (Efield (Evar _erval (Tstruct _asn_enc_rval_s noattr))
                      _encoded tint)
                    (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                  (Ssequence
                    (Sassign
                      (Efield (Evar _erval (Tstruct _asn_enc_rval_s noattr))
                        _failed_type
                        (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                      (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Evar _erval (Tstruct _asn_enc_rval_s noattr))
                          _structure_ptr (tptr tvoid))
                        (Etempvar _sptr (tptr tvoid)))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                            (Tstruct _asn_enc_rval_s noattr))
                          (Evar _erval (Tstruct _asn_enc_rval_s noattr)))
                        (Sreturn None)))))
                Sskip)))
          Sskip)
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield (Evar _erval (Tstruct _asn_enc_rval_s noattr)) _encoded
                tint))
            (Sassign
              (Efield (Evar _erval (Tstruct _asn_enc_rval_s noattr)) _encoded
                tint)
              (Ebinop Oadd (Etempvar _t'4 tint)
                (Econst_int (Int.repr 1) tint) tint)))
          (Sloop
            (Ssequence
              (Sassign
                (Efield (Evar _erval (Tstruct _asn_enc_rval_s noattr))
                  _structure_ptr (tptr tvoid))
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Efield (Evar _erval (Tstruct _asn_enc_rval_s noattr))
                    _failed_type
                    (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                      (Tstruct _asn_enc_rval_s noattr))
                    (Evar _erval (Tstruct _asn_enc_rval_s noattr)))
                  (Sreturn None))))
            Sbreak))))))
|}.

Definition f_BOOLEAN__xer_body_decode := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr tvoid)) :: (_chunk_buf, (tptr tvoid)) ::
                (_chunk_size, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_st, (tptr tint)) :: (_p, (tptr tschar)) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'4, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _st (Ecast (Etempvar _sptr (tptr tvoid)) (tptr tint)))
  (Ssequence
    (Sset _p (Ecast (Etempvar _chunk_buf (tptr tvoid)) (tptr tschar)))
    (Ssequence
      (Sifthenelse (Etempvar _chunk_size tuint)
        (Ssequence
          (Sset _t'4
            (Ederef
              (Ebinop Oadd (Etempvar _p (tptr tschar))
                (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar))
          (Sset _t'3
            (Ecast
              (Ebinop Oeq (Etempvar _t'4 tschar)
                (Econst_int (Int.repr 60) tint) tint) tbool)))
        (Sset _t'3 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'3 tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _xer_check_tag (Tfunction
                                     (Tcons (tptr tvoid)
                                       (Tcons tint
                                         (Tcons (tptr tschar) Tnil))) tint
                                     cc_default))
              ((Etempvar _chunk_buf (tptr tvoid)) ::
               (Etempvar _chunk_size tuint) ::
               (Evar ___stringlit_2 (tarray tschar 6)) :: nil))
            (Sswitch (Etempvar _t'1 tint)
              (LScons (Some 3)
                (Ssequence
                  (Sassign (Ederef (Etempvar _st (tptr tint)) tint)
                    (Econst_int (Int.repr 0) tint))
                  Sbreak)
                (LScons (Some 7)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _xer_check_tag (Tfunction
                                               (Tcons (tptr tvoid)
                                                 (Tcons tint
                                                   (Tcons (tptr tschar) Tnil)))
                                               tint cc_default))
                        ((Etempvar _chunk_buf (tptr tvoid)) ::
                         (Etempvar _chunk_size tuint) ::
                         (Evar ___stringlit_3 (tarray tschar 5)) :: nil))
                      (Sifthenelse (Ebinop One (Etempvar _t'2 tint)
                                     (Econst_int (Int.repr 3) tint) tint)
                        (Sreturn (Some (Econst_int (Int.repr 2) tint)))
                        Sskip))
                    (Ssequence
                      (Sassign (Ederef (Etempvar _st (tptr tint)) tint)
                        (Econst_int (Int.repr 1) tint))
                      Sbreak))
                  (LScons None
                    (Sreturn (Some (Econst_int (Int.repr 2) tint)))
                    LSnil)))))
          (Sreturn (Some (Econst_int (Int.repr 4) tint))))
        (Sreturn (Some (Econst_int (Int.repr 2) tint)))))))
|}.

Definition f_BOOLEAN_decode_xer := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_dec_rval_s noattr))) ::
                (_opt_codec_ctx, (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr (tptr tvoid))) ::
                (_opt_mname, (tptr tschar)) :: (_buf_ptr, (tptr tvoid)) ::
                (_size, tuint) :: nil);
  fn_vars := ((__res__1, (Tstruct _asn_dec_rval_s noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _xer_decode_primitive (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _asn_dec_rval_s noattr))
                                      (Tcons
                                        (tptr (Tstruct _asn_codec_ctx_s noattr))
                                        (Tcons
                                          (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                          (Tcons (tptr (tptr tvoid))
                                            (Tcons tuint
                                              (Tcons (tptr tschar)
                                                (Tcons (tptr tvoid)
                                                  (Tcons tuint
                                                    (Tcons
                                                      (tptr (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))))
                                                              tint
                                                              cc_default))
                                                      Tnil))))))))) tvoid
                                    {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
      ((Eaddrof (Evar __res__1 (Tstruct _asn_dec_rval_s noattr))
         (tptr (Tstruct _asn_dec_rval_s noattr))) ::
       (Etempvar _opt_codec_ctx (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
       (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
       (Etempvar _sptr (tptr (tptr tvoid))) :: (Esizeof tint tuint) ::
       (Etempvar _opt_mname (tptr tschar)) ::
       (Etempvar _buf_ptr (tptr tvoid)) :: (Etempvar _size tuint) ::
       (Evar _BOOLEAN__xer_body_decode (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                           (Tcons (tptr tvoid)
                                             (Tcons (tptr tvoid)
                                               (Tcons tuint Tnil)))) tint
                                         cc_default)) :: nil))
    (Sassign
      (Ederef (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
        (Tstruct _asn_dec_rval_s noattr))
      (Evar __res__1 (Tstruct _asn_dec_rval_s noattr))))
  (Sreturn None))
|}.

Definition f_BOOLEAN_encode_xer := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_enc_rval_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr tvoid)) :: (_ilevel, tint) :: (_flags, tint) ::
                (_cb,
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                         cc_default))) :: (_app_key, (tptr tvoid)) :: nil);
  fn_vars := ((_er, (Tstruct _asn_enc_rval_s noattr)) ::
              (_tmp_error, (Tstruct _asn_enc_rval_s noattr)) ::
              (_tmp_error__1, (Tstruct _asn_enc_rval_s noattr)) :: nil);
  fn_temps := ((_st, (tptr tint)) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _st (Ecast (Etempvar _sptr (tptr tvoid)) (tptr tint)))
  (Ssequence
    (Sassign
      (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _encoded tint)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _failed_type
          (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _structure_ptr
            (tptr tvoid)) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sifthenelse (Eunop Onotbool (Etempvar _st (tptr tint)) tint)
            (Sloop
              (Ssequence
                (Sassign
                  (Efield (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                    _encoded tint)
                  (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                      _failed_type
                      (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                    (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                        _structure_ptr (tptr tvoid))
                      (Etempvar _sptr (tptr tvoid)))
                    (Ssequence
                      (Sloop Sskip Sbreak)
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                            (Tstruct _asn_enc_rval_s noattr))
                          (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr)))
                        (Sreturn None))))))
              Sbreak)
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _t'3 (Ederef (Etempvar _st (tptr tint)) tint))
              (Sifthenelse (Etempvar _t'3 tint)
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'1)
                        (Etempvar _cb (tptr (Tfunction
                                              (Tcons (tptr tvoid)
                                                (Tcons tuint
                                                  (Tcons (tptr tvoid) Tnil)))
                                              tint cc_default)))
                        ((Evar ___stringlit_5 (tarray tschar 8)) ::
                         (Econst_int (Int.repr 7) tint) ::
                         (Etempvar _app_key (tptr tvoid)) :: nil))
                      (Sifthenelse (Ebinop Olt (Etempvar _t'1 tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Sgoto _cb_failed)
                        Sskip))
                    (Ssequence
                      (Sset _t'5
                        (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                          _encoded tint))
                      (Sassign
                        (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                          _encoded tint)
                        (Ebinop Oadd (Etempvar _t'5 tint)
                          (Econst_int (Int.repr 7) tint) tint))))
                  Sbreak)
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'2)
                        (Etempvar _cb (tptr (Tfunction
                                              (Tcons (tptr tvoid)
                                                (Tcons tuint
                                                  (Tcons (tptr tvoid) Tnil)))
                                              tint cc_default)))
                        ((Evar ___stringlit_4 (tarray tschar 9)) ::
                         (Econst_int (Int.repr 8) tint) ::
                         (Etempvar _app_key (tptr tvoid)) :: nil))
                      (Sifthenelse (Ebinop Olt (Etempvar _t'2 tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Sgoto _cb_failed)
                        Sskip))
                    (Ssequence
                      (Sset _t'4
                        (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                          _encoded tint))
                      (Sassign
                        (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                          _encoded tint)
                        (Ebinop Oadd (Etempvar _t'4 tint)
                          (Econst_int (Int.repr 8) tint) tint))))
                  Sbreak)))
            (Ssequence
              (Sloop
                (Ssequence
                  (Sassign
                    (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                      _structure_ptr (tptr tvoid))
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                        _failed_type
                        (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                      (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                          (Tstruct _asn_enc_rval_s noattr))
                        (Evar _er (Tstruct _asn_enc_rval_s noattr)))
                      (Sreturn None))))
                Sbreak)
              (Slabel _cb_failed
                (Sloop
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                        _encoded tint)
                      (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                          _failed_type
                          (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                        (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                            _structure_ptr (tptr tvoid))
                          (Etempvar _sptr (tptr tvoid)))
                        (Ssequence
                          (Sloop Sskip Sbreak)
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                                (Tstruct _asn_enc_rval_s noattr))
                              (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr)))
                            (Sreturn None))))))
                  Sbreak)))))))))
|}.

Definition f_BOOLEAN_print := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr tvoid)) :: (_ilevel, tint) ::
                (_cb,
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                         cc_default))) :: (_app_key, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_st, (tptr tint)) :: (_buf, (tptr tschar)) ::
               (_buflen, tuint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _st (Ecast (Etempvar _sptr (tptr tvoid)) (tptr tint)))
  (Ssequence
    (Sifthenelse (Etempvar _st (tptr tint))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _st (tptr tint)) tint))
        (Sifthenelse (Etempvar _t'3 tint)
          (Ssequence
            (Sset _buf (Evar ___stringlit_8 (tarray tschar 5)))
            (Sset _buflen (Econst_int (Int.repr 4) tint)))
          (Ssequence
            (Sset _buf (Evar ___stringlit_7 (tarray tschar 6)))
            (Sset _buflen (Econst_int (Int.repr 5) tint)))))
      (Ssequence
        (Sset _buf (Evar ___stringlit_6 (tarray tschar 9)))
        (Sset _buflen (Econst_int (Int.repr 8) tint))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Etempvar _cb (tptr (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                                tint cc_default)))
          ((Etempvar _buf (tptr tschar)) :: (Etempvar _buflen tuint) ::
           (Etempvar _app_key (tptr tvoid)) :: nil))
        (Sifthenelse (Ebinop Olt (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sset _t'2
            (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint))
          (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tint))))
      (Sreturn (Some (Etempvar _t'2 tint))))))
|}.

Definition f_BOOLEAN_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_ptr, (tptr tvoid)) :: (_method, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
    (Sset _t'1 (Ecast (Etempvar _ptr (tptr tvoid)) tbool))
    (Sset _t'1 (Econst_int (Int.repr 0) tint)))
  (Sifthenelse (Etempvar _t'1 tint)
    (Sswitch (Etempvar _method tint)
      (LScons (Some 0)
        (Ssequence
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default)) ((Etempvar _ptr (tptr tvoid)) :: nil))
          Sbreak)
        (LScons (Some 1)
          Sbreak
          (LScons (Some 2)
            (Ssequence
              (Scall None
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Etempvar _ptr (tptr tvoid)) ::
                 (Econst_int (Int.repr 0) tint) :: (Esizeof tint tuint) ::
                 nil))
              Sbreak)
            LSnil))))
    Sskip))
|}.

Definition f_BOOLEAN_decode_uper := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_dec_rval_s noattr))) ::
                (_opt_codec_ctx, (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_constraints,
                 (tptr (Tstruct _asn_per_constraints_s noattr))) ::
                (_sptr, (tptr (tptr tvoid))) ::
                (_pd, (tptr (Tstruct _asn_bit_data_s noattr))) :: nil);
  fn_vars := ((_rv, (Tstruct _asn_dec_rval_s noattr)) ::
              (_tmp_error, (Tstruct _asn_dec_rval_s noattr)) ::
              (_tmp_error__1, (Tstruct _asn_dec_rval_s noattr)) :: nil);
  fn_temps := ((_st, (tptr tint)) :: (_t'3, tint) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: (_t'4, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4 (Ederef (Etempvar _sptr (tptr (tptr tvoid))) (tptr tvoid)))
    (Sset _st (Ecast (Etempvar _t'4 (tptr tvoid)) (tptr tint))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _st (tptr tint)) tint)
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                cc_default)) ((Esizeof tint tuint) :: nil))
              (Sset _t'2 (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tvoid))))
            (Sassign
              (Ederef (Etempvar _sptr (tptr (tptr tvoid))) (tptr tvoid))
              (Etempvar _t'2 (tptr tvoid))))
          (Sset _st (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tint))))
        (Sifthenelse (Eunop Onotbool (Etempvar _st (tptr tint)) tint)
          (Sloop
            (Ssequence
              (Sassign
                (Efield (Evar _tmp_error (Tstruct _asn_dec_rval_s noattr))
                  _code tint) (Econst_int (Int.repr 2) tint))
              (Ssequence
                (Sassign
                  (Efield (Evar _tmp_error (Tstruct _asn_dec_rval_s noattr))
                    _consumed tuint) (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sloop Sskip Sbreak)
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                        (Tstruct _asn_dec_rval_s noattr))
                      (Evar _tmp_error (Tstruct _asn_dec_rval_s noattr)))
                    (Sreturn None)))))
            Sbreak)
          Sskip))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _asn_get_few_bits (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _asn_bit_data_s noattr))
                                      (Tcons tint Tnil)) tint cc_default))
          ((Etempvar _pd (tptr (Tstruct _asn_bit_data_s noattr))) ::
           (Econst_int (Int.repr 1) tint) :: nil))
        (Sswitch (Etempvar _t'3 tint)
          (LScons (Some 1)
            (Ssequence
              (Sassign (Ederef (Etempvar _st (tptr tint)) tint)
                (Econst_int (Int.repr 1) tint))
              Sbreak)
            (LScons (Some 0)
              (Ssequence
                (Sassign (Ederef (Etempvar _st (tptr tint)) tint)
                  (Econst_int (Int.repr 0) tint))
                Sbreak)
              (LScons (Some 4294967295)
                Sskip
                (LScons None
                  (Sloop
                    (Ssequence
                      (Sassign
                        (Efield
                          (Evar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr))
                          _code tint) (Econst_int (Int.repr 1) tint))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Evar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr))
                            _consumed tuint) (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                              (Tstruct _asn_dec_rval_s noattr))
                            (Evar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr)))
                          (Sreturn None))))
                    Sbreak)
                  LSnil))))))
      (Ssequence
        (Sloop Sskip Sbreak)
        (Ssequence
          (Sassign
            (Efield (Evar _rv (Tstruct _asn_dec_rval_s noattr)) _code tint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield (Evar _rv (Tstruct _asn_dec_rval_s noattr)) _consumed
                tuint) (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                  (Tstruct _asn_dec_rval_s noattr))
                (Evar _rv (Tstruct _asn_dec_rval_s noattr)))
              (Sreturn None))))))))
|}.

Definition f_BOOLEAN_encode_uper := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_enc_rval_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_constraints,
                 (tptr (Tstruct _asn_per_constraints_s noattr))) ::
                (_sptr, (tptr tvoid)) ::
                (_po, (tptr (Tstruct _asn_bit_outp_s noattr))) :: nil);
  fn_vars := ((_er, (Tstruct _asn_enc_rval_s noattr)) ::
              (_tmp_error, (Tstruct _asn_enc_rval_s noattr)) ::
              (_tmp_error__1, (Tstruct _asn_enc_rval_s noattr)) :: nil);
  fn_temps := ((_st, (tptr tint)) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _st (Ecast (Etempvar _sptr (tptr tvoid)) (tptr tint)))
  (Ssequence
    (Sassign
      (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _encoded tint)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _failed_type
          (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _structure_ptr
            (tptr tvoid)) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sifthenelse (Eunop Onotbool (Etempvar _st (tptr tint)) tint)
            (Sloop
              (Ssequence
                (Sassign
                  (Efield (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                    _encoded tint)
                  (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                      _failed_type
                      (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                    (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                        _structure_ptr (tptr tvoid))
                      (Etempvar _sptr (tptr tvoid)))
                    (Ssequence
                      (Sloop Sskip Sbreak)
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                            (Tstruct _asn_enc_rval_s noattr))
                          (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr)))
                        (Sreturn None))))))
              Sbreak)
            Sskip)
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'3 (Ederef (Etempvar _st (tptr tint)) tint))
                  (Sifthenelse (Etempvar _t'3 tint)
                    (Sset _t'1 (Ecast (Econst_int (Int.repr 1) tint) tint))
                    (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tint))))
                (Scall (Some _t'2)
                  (Evar _asn_put_few_bits (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _asn_bit_outp_s noattr))
                                              (Tcons tuint (Tcons tint Tnil)))
                                            tint cc_default))
                  ((Etempvar _po (tptr (Tstruct _asn_bit_outp_s noattr))) ::
                   (Etempvar _t'1 tint) :: (Econst_int (Int.repr 1) tint) ::
                   nil)))
              (Sifthenelse (Etempvar _t'2 tint)
                (Sloop
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                        _encoded tint)
                      (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                          _failed_type
                          (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                        (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr))
                            _structure_ptr (tptr tvoid))
                          (Etempvar _sptr (tptr tvoid)))
                        (Ssequence
                          (Sloop Sskip Sbreak)
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                                (Tstruct _asn_enc_rval_s noattr))
                              (Evar _tmp_error__1 (Tstruct _asn_enc_rval_s noattr)))
                            (Sreturn None))))))
                  Sbreak)
                Sskip))
            (Sloop
              (Ssequence
                (Sassign
                  (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                    _structure_ptr (tptr tvoid))
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                      _failed_type
                      (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                        (Tstruct _asn_enc_rval_s noattr))
                      (Evar _er (Tstruct _asn_enc_rval_s noattr)))
                    (Sreturn None))))
              Sbreak)))))))
|}.

Definition f_BOOLEAN_encode_oer := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_enc_rval_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_constraints,
                 (tptr (Tstruct _asn_oer_constraints_s noattr))) ::
                (_sptr, (tptr tvoid)) ::
                (_cb,
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                         cc_default))) :: (_app_key, (tptr tvoid)) :: nil);
  fn_vars := ((_er, (Tstruct _asn_enc_rval_s noattr)) ::
              (_bool_value, tuchar) ::
              (_tmp_error, (Tstruct _asn_enc_rval_s noattr)) :: nil);
  fn_temps := ((_st, (tptr tint)) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _encoded tint)
    (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sassign
      (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _failed_type
        (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr)) _structure_ptr
          (tptr tvoid)) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _st (Etempvar _sptr (tptr tvoid)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'3 (Ederef (Etempvar _st (tptr tint)) tint))
              (Sifthenelse (Etempvar _t'3 tint)
                (Sset _t'1 (Ecast (Econst_int (Int.repr 255) tint) tint))
                (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tint))))
            (Sassign (Evar _bool_value tuchar) (Etempvar _t'1 tint)))
          (Ssequence
            (Scall (Some _t'2)
              (Etempvar _cb (tptr (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                                    tint cc_default)))
              ((Eaddrof (Evar _bool_value tuchar) (tptr tuchar)) ::
               (Econst_int (Int.repr 1) tint) ::
               (Etempvar _app_key (tptr tvoid)) :: nil))
            (Sifthenelse (Ebinop Olt (Etempvar _t'2 tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sloop
                (Ssequence
                  (Sassign
                    (Efield
                      (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                      _encoded tint)
                    (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                        _failed_type
                        (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                      (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr))
                          _structure_ptr (tptr tvoid))
                        (Etempvar _sptr (tptr tvoid)))
                      (Ssequence
                        (Sloop Sskip Sbreak)
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                              (Tstruct _asn_enc_rval_s noattr))
                            (Evar _tmp_error (Tstruct _asn_enc_rval_s noattr)))
                          (Sreturn None))))))
                Sbreak)
              (Sloop
                (Ssequence
                  (Sassign
                    (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                      _structure_ptr (tptr tvoid))
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Efield (Evar _er (Tstruct _asn_enc_rval_s noattr))
                        _failed_type
                        (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                      (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Etempvar __res (tptr (Tstruct _asn_enc_rval_s noattr)))
                          (Tstruct _asn_enc_rval_s noattr))
                        (Evar _er (Tstruct _asn_enc_rval_s noattr)))
                      (Sreturn None))))
                Sbreak))))))))
|}.

Definition f_BOOLEAN_decode_oer := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_dec_rval_s noattr))) ::
                (_opt_codec_ctx, (tptr (Tstruct _asn_codec_ctx_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_constraints,
                 (tptr (Tstruct _asn_oer_constraints_s noattr))) ::
                (_sptr, (tptr (tptr tvoid))) :: (_ptr, (tptr tvoid)) ::
                (_size, tuint) :: nil);
  fn_vars := ((_ok, (Tstruct _asn_dec_rval_s noattr)) ::
              (_tmp_error, (Tstruct _asn_dec_rval_s noattr)) ::
              (_tmp_error__1, (Tstruct _asn_dec_rval_s noattr)) :: nil);
  fn_temps := ((_st, (tptr tint)) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'5, (tptr tvoid)) :: (_t'4, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _ok (Tstruct _asn_dec_rval_s noattr)) _code tint)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield (Evar _ok (Tstruct _asn_dec_rval_s noattr)) _consumed tuint)
      (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _size tuint)
                     (Econst_int (Int.repr 1) tint) tint)
        (Sloop
          (Ssequence
            (Sassign
              (Efield (Evar _tmp_error (Tstruct _asn_dec_rval_s noattr))
                _code tint) (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sassign
                (Efield (Evar _tmp_error (Tstruct _asn_dec_rval_s noattr))
                  _consumed tuint) (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                    (Tstruct _asn_dec_rval_s noattr))
                  (Evar _tmp_error (Tstruct _asn_dec_rval_s noattr)))
                (Sreturn None))))
          Sbreak)
        Sskip)
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'5
                (Ederef (Etempvar _sptr (tptr (tptr tvoid))) (tptr tvoid)))
              (Sset _t'3 (Ecast (Etempvar _t'5 (tptr tvoid)) (tptr tint))))
            (Sset _st (Etempvar _t'3 (tptr tint))))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'3 (tptr tint)) tint)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'1)
                      (Evar _calloc (Tfunction
                                      (Tcons tuint (Tcons tuint Tnil))
                                      (tptr tvoid) cc_default))
                      ((Econst_int (Int.repr 1) tint) ::
                       (Esizeof tint tuint) :: nil))
                    (Sset _t'2
                      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tvoid))))
                  (Sassign
                    (Ederef (Etempvar _sptr (tptr (tptr tvoid)))
                      (tptr tvoid)) (Etempvar _t'2 (tptr tvoid))))
                (Sset _st (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tint))))
              (Sifthenelse (Eunop Onotbool (Etempvar _st (tptr tint)) tint)
                (Sloop
                  (Ssequence
                    (Sassign
                      (Efield
                        (Evar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr))
                        _code tint) (Econst_int (Int.repr 2) tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Evar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr))
                          _consumed tuint) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sloop Sskip Sbreak)
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                              (Tstruct _asn_dec_rval_s noattr))
                            (Evar _tmp_error__1 (Tstruct _asn_dec_rval_s noattr)))
                          (Sreturn None)))))
                  Sbreak)
                Sskip))
            Sskip))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Ederef (Ecast (Etempvar _ptr (tptr tvoid)) (tptr tuchar))
                tuchar))
            (Sassign (Ederef (Etempvar _st (tptr tint)) tint)
              (Etempvar _t'4 tuchar)))
          (Ssequence
            (Sassign
              (Ederef
                (Etempvar __res (tptr (Tstruct _asn_dec_rval_s noattr)))
                (Tstruct _asn_dec_rval_s noattr))
              (Evar _ok (Tstruct _asn_dec_rval_s noattr)))
            (Sreturn None)))))))
|}.

Definition f_BOOLEAN_compare := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_aptr, (tptr tvoid)) :: (_bptr, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_a, (tptr tint)) :: (_b, (tptr tint)) :: (_t'1, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _a (Etempvar _aptr (tptr tvoid)))
  (Ssequence
    (Sset _b (Etempvar _bptr (tptr tvoid)))
    (Ssequence
      (Sifthenelse (Etempvar _a (tptr tint))
        (Sset _t'1 (Ecast (Etempvar _b (tptr tint)) tbool))
        (Sset _t'1 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'1 tint)
        (Ssequence
          (Sset _t'2 (Ederef (Etempvar _a (tptr tint)) tint))
          (Ssequence
            (Sset _t'3 (Ederef (Etempvar _b (tptr tint)) tint))
            (Sifthenelse (Ebinop Oeq
                           (Eunop Onotbool (Etempvar _t'2 tint) tint)
                           (Eunop Onotbool (Etempvar _t'3 tint) tint) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              (Ssequence
                (Sset _t'4 (Ederef (Etempvar _a (tptr tint)) tint))
                (Sifthenelse (Eunop Onotbool (Etempvar _t'4 tint) tint)
                  (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                   tint)))
                  (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))
        (Sifthenelse (Eunop Onotbool (Etempvar _a (tptr tint)) tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
          (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))
|}.

Definition f_BOOLEAN_random_fill := {|
  fn_return := tvoid;
  fn_callconv := {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|};
  fn_params := ((__res, (tptr (Tstruct _asn_random_fill_result_s noattr))) ::
                (_td, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
                (_sptr, (tptr (tptr tvoid))) ::
                (_constraints,
                 (tptr (Tstruct _asn_encoding_constraints_s noattr))) ::
                (_max_length, tuint) :: nil);
  fn_vars := ((_result_ok, (Tstruct _asn_random_fill_result_s noattr)) ::
              (_result_failed, (Tstruct _asn_random_fill_result_s noattr)) ::
              (_result_skipped, (Tstruct _asn_random_fill_result_s noattr)) ::
              nil);
  fn_temps := ((_st, (tptr tint)) ::
               (_pc, (tptr (Tstruct _asn_per_constraint_s noattr))) ::
               (_t'6, tlong) :: (_t'5, tlong) :: (_t'4, tlong) ::
               (_t'3, tint) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) ::
               (_t'12, (tptr (Tstruct _asn_per_constraints_s noattr))) ::
               (_t'11, (tptr (Tstruct _asn_per_constraints_s noattr))) ::
               (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, (tptr (Tstruct _asn_per_constraints_s noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield (Evar _result_ok (Tstruct _asn_random_fill_result_s noattr))
      _code tint) (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield (Evar _result_ok (Tstruct _asn_random_fill_result_s noattr))
        _length tuint) (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Sassign
        (Efield
          (Evar _result_failed (Tstruct _asn_random_fill_result_s noattr))
          _code tint) (Econst_int (Int.repr (-1)) tint))
      (Ssequence
        (Sassign
          (Efield
            (Evar _result_failed (Tstruct _asn_random_fill_result_s noattr))
            _length tuint) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Evar _result_skipped (Tstruct _asn_random_fill_result_s noattr))
              _code tint) (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Sassign
              (Efield
                (Evar _result_skipped (Tstruct _asn_random_fill_result_s noattr))
                _length tuint) (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sset _st
                (Ederef (Etempvar _sptr (tptr (tptr tvoid))) (tptr tvoid)))
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _max_length tuint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Etempvar __res (tptr (Tstruct _asn_random_fill_result_s noattr)))
                        (Tstruct _asn_random_fill_result_s noattr))
                      (Evar _result_skipped (Tstruct _asn_random_fill_result_s noattr)))
                    (Sreturn None))
                  Sskip)
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _st (tptr tint))
                                 (Ecast (Econst_int (Int.repr 0) tint)
                                   (tptr tvoid)) tint)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'1)
                              (Evar _calloc (Tfunction
                                              (Tcons tuint
                                                (Tcons tuint Tnil))
                                              (tptr tvoid) cc_default))
                              ((Econst_int (Int.repr 1) tint) ::
                               (Esizeof tint tuint) :: nil))
                            (Sset _t'2
                              (Ecast (Etempvar _t'1 (tptr tvoid))
                                (tptr tvoid))))
                          (Sassign
                            (Ederef (Etempvar _sptr (tptr (tptr tvoid)))
                              (tptr tvoid)) (Etempvar _t'2 (tptr tvoid))))
                        (Sset _st
                          (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tint))))
                      (Sifthenelse (Ebinop Oeq (Etempvar _st (tptr tint))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Etempvar __res (tptr (Tstruct _asn_random_fill_result_s noattr)))
                              (Tstruct _asn_random_fill_result_s noattr))
                            (Evar _result_failed (Tstruct _asn_random_fill_result_s noattr)))
                          (Sreturn None))
                        Sskip))
                    Sskip)
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Eunop Onotbool
                                     (Etempvar _constraints (tptr (Tstruct _asn_encoding_constraints_s noattr)))
                                     tint)
                        (Sset _t'3 (Econst_int (Int.repr 1) tint))
                        (Ssequence
                          (Sset _t'12
                            (Efield
                              (Ederef
                                (Etempvar _constraints (tptr (Tstruct _asn_encoding_constraints_s noattr)))
                                (Tstruct _asn_encoding_constraints_s noattr))
                              _per_constraints
                              (tptr (Tstruct _asn_per_constraints_s noattr))))
                          (Sset _t'3
                            (Ecast
                              (Eunop Onotbool
                                (Etempvar _t'12 (tptr (Tstruct _asn_per_constraints_s noattr)))
                                tint) tbool))))
                      (Sifthenelse (Etempvar _t'3 tint)
                        (Sset _constraints
                          (Eaddrof
                            (Efield
                              (Ederef
                                (Etempvar _td (tptr (Tstruct _asn_TYPE_descriptor_s noattr)))
                                (Tstruct _asn_TYPE_descriptor_s noattr))
                              _encoding_constraints
                              (Tstruct _asn_encoding_constraints_s noattr))
                            (tptr (Tstruct _asn_encoding_constraints_s noattr))))
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Sset _t'7
                          (Efield
                            (Ederef
                              (Etempvar _constraints (tptr (Tstruct _asn_encoding_constraints_s noattr)))
                              (Tstruct _asn_encoding_constraints_s noattr))
                            _per_constraints
                            (tptr (Tstruct _asn_per_constraints_s noattr))))
                        (Sifthenelse (Etempvar _t'7 (tptr (Tstruct _asn_per_constraints_s noattr)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'11
                                (Efield
                                  (Ederef
                                    (Etempvar _constraints (tptr (Tstruct _asn_encoding_constraints_s noattr)))
                                    (Tstruct _asn_encoding_constraints_s noattr))
                                  _per_constraints
                                  (tptr (Tstruct _asn_per_constraints_s noattr))))
                              (Sset _pc
                                (Eaddrof
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'11 (tptr (Tstruct _asn_per_constraints_s noattr)))
                                      (Tstruct _asn_per_constraints_s noattr))
                                    _value
                                    (Tstruct _asn_per_constraint_s noattr))
                                  (tptr (Tstruct _asn_per_constraint_s noattr)))))
                            (Ssequence
                              (Sset _t'8
                                (Efield
                                  (Ederef
                                    (Etempvar _pc (tptr (Tstruct _asn_per_constraint_s noattr)))
                                    (Tstruct _asn_per_constraint_s noattr))
                                  _flags tint))
                              (Sifthenelse (Ebinop Oand (Etempvar _t'8 tint)
                                             (Econst_int (Int.repr 2) tint)
                                             tint)
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Ederef
                                            (Etempvar _pc (tptr (Tstruct _asn_per_constraint_s noattr)))
                                            (Tstruct _asn_per_constraint_s noattr))
                                          _lower_bound tint))
                                      (Ssequence
                                        (Sset _t'10
                                          (Efield
                                            (Ederef
                                              (Etempvar _pc (tptr (Tstruct _asn_per_constraint_s noattr)))
                                              (Tstruct _asn_per_constraint_s noattr))
                                            _upper_bound tint))
                                        (Scall (Some _t'4)
                                          (Evar _asn_random_between (Tfunction
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tlong
                                                                    Tnil))
                                                                    tlong
                                                                    cc_default))
                                          ((Etempvar _t'9 tint) ::
                                           (Etempvar _t'10 tint) :: nil))))
                                    (Sassign
                                      (Ederef (Etempvar _st (tptr tint))
                                        tint) (Etempvar _t'4 tlong)))
                                  (Ssequence
                                    (Sassign
                                      (Ederef
                                        (Etempvar __res (tptr (Tstruct _asn_random_fill_result_s noattr)))
                                        (Tstruct _asn_random_fill_result_s noattr))
                                      (Evar _result_ok (Tstruct _asn_random_fill_result_s noattr)))
                                    (Sreturn None)))
                                Sskip)))
                          Sskip))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar _asn_random_between (Tfunction
                                                        (Tcons tlong
                                                          (Tcons tlong Tnil))
                                                        tlong cc_default))
                            ((Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 7) tint) :: nil))
                          (Sswitch (Etempvar _t'5 tlong)
                            (LScons (Some 0)
                              Sskip
                              (LScons (Some 1)
                                Sskip
                                (LScons (Some 2)
                                  (Ssequence
                                    (Sassign
                                      (Ederef (Etempvar _st (tptr tint))
                                        tint) (Econst_int (Int.repr 0) tint))
                                    Sbreak)
                                  (LScons (Some 3)
                                    (Ssequence
                                      (Sassign
                                        (Ederef (Etempvar _st (tptr tint))
                                          tint)
                                        (Eunop Oneg
                                          (Econst_int (Int.repr 1) tint)
                                          tint))
                                      Sbreak)
                                    (LScons (Some 4)
                                      (Ssequence
                                        (Sassign
                                          (Ederef (Etempvar _st (tptr tint))
                                            tint)
                                          (Econst_int (Int.repr 1) tint))
                                        Sbreak)
                                      (LScons (Some 5)
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Etempvar _st (tptr tint))
                                              tint)
                                            (Ebinop Osub
                                              (Eunop Oneg
                                                (Econst_int (Int.repr 2147483647) tint)
                                                tint)
                                              (Econst_int (Int.repr 1) tint)
                                              tint))
                                          Sbreak)
                                        (LScons (Some 6)
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Etempvar _st (tptr tint))
                                                tint)
                                              (Econst_int (Int.repr 2147483647) tint))
                                            Sbreak)
                                          (LScons None
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'6)
                                                  (Evar _asn_random_between 
                                                  (Tfunction
                                                    (Tcons tlong
                                                      (Tcons tlong Tnil))
                                                    tlong cc_default))
                                                  ((Ebinop Osub
                                                     (Eunop Oneg
                                                       (Econst_int (Int.repr 2147483647) tint)
                                                       tint)
                                                     (Econst_int (Int.repr 1) tint)
                                                     tint) ::
                                                   (Econst_int (Int.repr 2147483647) tint) ::
                                                   nil))
                                                (Sassign
                                                  (Ederef
                                                    (Etempvar _st (tptr tint))
                                                    tint)
                                                  (Etempvar _t'6 tlong)))
                                              Sbreak)
                                            LSnil))))))))))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Etempvar __res (tptr (Tstruct _asn_random_fill_result_s noattr)))
                              (Tstruct _asn_random_fill_result_s noattr))
                            (Evar _result_ok (Tstruct _asn_random_fill_result_s noattr)))
                          (Sreturn None))))))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _asn_codec_ctx_s Struct ((_max_stack_size, tuint) :: nil) noattr ::
 Composite _asn_enc_rval_s Struct
   ((_encoded, tint) ::
    (_failed_type, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
    (_structure_ptr, (tptr tvoid)) :: nil)
   noattr ::
 Composite _asn_dec_rval_s Struct
   ((_code, tint) :: (_consumed, tuint) :: nil)
   noattr ::
 Composite _asn_struct_ctx_s Struct
   ((_phase, tshort) :: (_step, tshort) :: (_context, tint) ::
    (_ptr, (tptr tvoid)) :: (_left, tint) :: nil)
   noattr ::
 Composite _asn_bit_data_s Struct
   ((_buffer, (tptr tuchar)) :: (_nboff, tuint) :: (_nbits, tuint) ::
    (_moved, tuint) ::
    (_refill,
     (tptr (Tfunction (Tcons (tptr (Tstruct _asn_bit_data_s noattr)) Tnil)
             tint cc_default))) :: (_refill_key, (tptr tvoid)) :: nil)
   noattr ::
 Composite _asn_bit_outp_s Struct
   ((_buffer, (tptr tuchar)) :: (_nboff, tuint) :: (_nbits, tuint) ::
    (_tmpspace, (tarray tuchar 32)) ::
    (_output,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons tuint (Tcons (tptr tvoid) Tnil)))
             tint cc_default))) :: (_op_key, (tptr tvoid)) ::
    (_flushed_bytes, tuint) :: nil)
   noattr ::
 Composite _asn_per_constraint_s Struct
   ((_flags, tint) :: (_range_bits, tint) :: (_effective_bits, tint) ::
    (_lower_bound, tint) :: (_upper_bound, tint) :: nil)
   noattr ::
 Composite _asn_per_constraints_s Struct
   ((_value, (Tstruct _asn_per_constraint_s noattr)) ::
    (_size, (Tstruct _asn_per_constraint_s noattr)) ::
    (_value2code, (tptr (Tfunction (Tcons tuint Tnil) tint cc_default))) ::
    (_code2value, (tptr (Tfunction (Tcons tuint Tnil) tint cc_default))) ::
    nil)
   noattr ::
 Composite _asn_random_fill_result_s Struct
   ((_code, tint) :: (_length, tuint) :: nil)
   noattr ::
 Composite _asn_oer_constraint_number_s Struct
   ((_width, tuint) :: (_positive, tuint) :: nil)
   noattr ::
 Composite _asn_oer_constraints_s Struct
   ((_value, (Tstruct _asn_oer_constraint_number_s noattr)) ::
    (_size, tint) :: nil)
   noattr ::
 Composite _asn_type_selector_result_s Struct
   ((_type_descriptor, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
    (_presence_index, tuint) :: nil)
   noattr ::
 Composite _asn_TYPE_operation_s Struct
   ((_free_struct,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
               (Tcons (tptr tvoid) (Tcons tint Tnil))) tvoid cc_default))) ::
    (_print_struct,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
               (Tcons (tptr tvoid)
                 (Tcons tint
                   (Tcons
                     (tptr (Tfunction
                             (Tcons (tptr tvoid)
                               (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                             cc_default)) (Tcons (tptr tvoid) Tnil))))) tint
             cc_default))) ::
    (_compare_struct,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
               (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil))) tint
             cc_default))) ::
    (_ber_decoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
                 (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                   (Tcons (tptr (tptr tvoid))
                     (Tcons (tptr tvoid) (Tcons tuint (Tcons tint Tnil)))))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_der_encoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr tvoid)
                   (Tcons tint
                     (Tcons tuint
                       (Tcons
                         (tptr (Tfunction
                                 (Tcons (tptr tvoid)
                                   (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                                 tint cc_default)) (Tcons (tptr tvoid) Tnil)))))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_xer_decoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
                 (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                   (Tcons (tptr (tptr tvoid))
                     (Tcons (tptr tschar)
                       (Tcons (tptr tvoid) (Tcons tuint Tnil))))))) tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_xer_encoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr tvoid)
                   (Tcons tint
                     (Tcons tint
                       (Tcons
                         (tptr (Tfunction
                                 (Tcons (tptr tvoid)
                                   (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                                 tint cc_default)) (Tcons (tptr tvoid) Tnil)))))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_oer_decoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
                 (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                   (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
                     (Tcons (tptr (tptr tvoid))
                       (Tcons (tptr tvoid) (Tcons tuint Tnil))))))) tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_oer_encoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
                   (Tcons (tptr tvoid)
                     (Tcons
                       (tptr (Tfunction
                               (Tcons (tptr tvoid)
                                 (Tcons tuint (Tcons (tptr tvoid) Tnil)))
                               tint cc_default)) (Tcons (tptr tvoid) Tnil))))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_uper_decoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
                 (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                   (Tcons (tptr (Tstruct _asn_per_constraints_s noattr))
                     (Tcons (tptr (tptr tvoid))
                       (Tcons (tptr (Tstruct _asn_bit_data_s noattr)) Tnil))))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_uper_encoder,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr (Tstruct _asn_per_constraints_s noattr))
                   (Tcons (tptr tvoid)
                     (Tcons (tptr (Tstruct _asn_bit_outp_s noattr)) Tnil)))))
             tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_random_fill,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_random_fill_result_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr (tptr tvoid))
                   (Tcons (tptr (Tstruct _asn_encoding_constraints_s noattr))
                     (Tcons tuint Tnil))))) tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_outmost_tag,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
               (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))) tuint
             cc_default))) :: nil)
   noattr ::
 Composite _asn_encoding_constraints_s Struct
   ((_oer_constraints, (tptr (Tstruct _asn_oer_constraints_s noattr))) ::
    (_per_constraints, (tptr (Tstruct _asn_per_constraints_s noattr))) ::
    (_general_constraints,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
               (Tcons (tptr tvoid)
                 (Tcons
                   (tptr (Tfunction
                           (Tcons (tptr tvoid)
                             (Tcons
                               (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                               (Tcons (tptr tvoid)
                                 (Tcons (tptr tschar) Tnil)))) tvoid
                           {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                   (Tcons (tptr tvoid) Tnil)))) tint cc_default))) :: nil)
   noattr ::
 Composite _asn_TYPE_descriptor_s Struct
   ((_name, (tptr tschar)) :: (_xml_tag, (tptr tschar)) ::
    (_op, (tptr (Tstruct _asn_TYPE_operation_s noattr))) ::
    (_tags, (tptr tuint)) :: (_tags_count, tuint) ::
    (_all_tags, (tptr tuint)) :: (_all_tags_count, tuint) ::
    (_encoding_constraints, (Tstruct _asn_encoding_constraints_s noattr)) ::
    (_elements, (tptr (Tstruct _asn_TYPE_member_s noattr))) ::
    (_elements_count, tuint) :: (_specifics, (tptr tvoid)) :: nil)
   noattr ::
 Composite _asn_TYPE_member_s Struct
   ((_flags, tint) :: (_optional, tuint) :: (_memb_offset, tuint) ::
    (_tag, tuint) :: (_tag_mode, tint) ::
    (_type, (tptr (Tstruct _asn_TYPE_descriptor_s noattr))) ::
    (_type_selector,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _asn_type_selector_result_s noattr))
               (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                 (Tcons (tptr tvoid) Tnil))) tvoid
             {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))) ::
    (_encoding_constraints, (Tstruct _asn_encoding_constraints_s noattr)) ::
    (_default_value_cmp,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default))) ::
    (_default_value_set,
     (tptr (Tfunction (Tcons (tptr (tptr tvoid)) Tnil) tint cc_default))) ::
    (_name, (tptr tschar)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_calloc,
   Gfun(External (EF_external "calloc"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tuint (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_ber_check_tags,
   Gfun(External (EF_external "ber_check_tags"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (Tstruct _asn_struct_ctx_s noattr))
             (Tcons (tptr tvoid)
               (Tcons tuint
                 (Tcons tint
                   (Tcons tint (Tcons (tptr tint) (Tcons (tptr tint) Tnil))))))))))
     tvoid {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_der_write_tags,
   Gfun(External (EF_external "der_write_tags"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons tuint
         (Tcons tint
           (Tcons tint
             (Tcons tuint
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                         cc_default)) (Tcons (tptr tvoid) Tnil))))))) tint
     cc_default)) ::
 (_xer_check_tag,
   Gfun(External (EF_external "xer_check_tag"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons (tptr tschar) Tnil))) tint
     cc_default)) ::
 (_asn_get_few_bits,
   Gfun(External (EF_external "asn_get_few_bits"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr (Tstruct _asn_bit_data_s noattr)) (Tcons tint Tnil)) tint
     cc_default)) ::
 (_asn_put_few_bits,
   Gfun(External (EF_external "asn_put_few_bits"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_bit_outp_s noattr))
       (Tcons tuint (Tcons tint Tnil))) tint cc_default)) ::
 (_asn_generic_no_constraint,
   Gfun(External (EF_external "asn_generic_no_constraint"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid)
         (Tcons
           (tptr (Tfunction
                   (Tcons (tptr tvoid)
                     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                       (Tcons (tptr tvoid) (Tcons (tptr tschar) Tnil))))
                   tvoid
                   {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
           (Tcons (tptr tvoid) Tnil)))) tint cc_default)) ::
 (_asn_generic_unknown_constraint,
   Gfun(External (EF_external "asn_generic_unknown_constraint"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid)
         (Tcons
           (tptr (Tfunction
                   (Tcons (tptr tvoid)
                     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                       (Tcons (tptr tvoid) (Tcons (tptr tschar) Tnil))))
                   tvoid
                   {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
           (Tcons (tptr tvoid) Tnil)))) tint cc_default)) ::
 (_asn_random_between,
   Gfun(External (EF_external "asn_random_between"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (_oer_decode_primitive,
   Gfun(External (EF_external "oer_decode_primitive"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
             (Tcons (tptr (tptr tvoid))
               (Tcons (tptr tvoid) (Tcons tuint Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_oer_encode_primitive,
   Gfun(External (EF_external "oer_encode_primitive"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr (Tstruct _asn_oer_constraints_s noattr))
           (Tcons (tptr tvoid)
             (Tcons
               (tptr (Tfunction
                       (Tcons (tptr tvoid)
                         (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                       cc_default)) (Tcons (tptr tvoid) Tnil)))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_asn_TYPE_outmost_tag,
   Gfun(External (EF_external "asn_TYPE_outmost_tag"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))) tuint
     cc_default)) ::
 (_ASN__PRIMITIVE_TYPE_free,
   Gfun(External (EF_external "ASN__PRIMITIVE_TYPE_free"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
       (Tcons (tptr tvoid) (Tcons tint Tnil))) tvoid cc_default)) ::
 (_ber_decode_primitive,
   Gfun(External (EF_external "ber_decode_primitive"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (tptr tvoid))
             (Tcons (tptr tvoid) (Tcons tuint (Tcons tint Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_der_encode_primitive,
   Gfun(External (EF_external "der_encode_primitive"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_enc_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
         (Tcons (tptr tvoid)
           (Tcons tint
             (Tcons tuint
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons tuint (Tcons (tptr tvoid) Tnil))) tint
                         cc_default)) (Tcons (tptr tvoid) Tnil))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_xer_decode_primitive,
   Gfun(External (EF_external "xer_decode_primitive"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: nil) None
                     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|}))
     (Tcons (tptr (Tstruct _asn_dec_rval_s noattr))
       (Tcons (tptr (Tstruct _asn_codec_ctx_s noattr))
         (Tcons (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
           (Tcons (tptr (tptr tvoid))
             (Tcons tuint
               (Tcons (tptr tschar)
                 (Tcons (tptr tvoid)
                   (Tcons tuint
                     (Tcons
                       (tptr (Tfunction
                               (Tcons
                                 (tptr (Tstruct _asn_TYPE_descriptor_s noattr))
                                 (Tcons (tptr tvoid)
                                   (Tcons (tptr tvoid) (Tcons tuint Tnil))))
                               tint cc_default)) Tnil))))))))) tvoid
     {|cc_vararg:=false; cc_unproto:=false; cc_structret:=true|})) ::
 (_asn_DEF_BOOLEAN_tags, Gvar v_asn_DEF_BOOLEAN_tags) ::
 (_asn_OP_BOOLEAN, Gvar v_asn_OP_BOOLEAN) ::
 (_asn_DEF_BOOLEAN, Gvar v_asn_DEF_BOOLEAN) ::
 (_BOOLEAN_decode_ber, Gfun(Internal f_BOOLEAN_decode_ber)) ::
 (_BOOLEAN_encode_der, Gfun(Internal f_BOOLEAN_encode_der)) ::
 (_BOOLEAN__xer_body_decode, Gfun(Internal f_BOOLEAN__xer_body_decode)) ::
 (_BOOLEAN_decode_xer, Gfun(Internal f_BOOLEAN_decode_xer)) ::
 (_BOOLEAN_encode_xer, Gfun(Internal f_BOOLEAN_encode_xer)) ::
 (_BOOLEAN_print, Gfun(Internal f_BOOLEAN_print)) ::
 (_BOOLEAN_free, Gfun(Internal f_BOOLEAN_free)) ::
 (_BOOLEAN_decode_uper, Gfun(Internal f_BOOLEAN_decode_uper)) ::
 (_BOOLEAN_encode_uper, Gfun(Internal f_BOOLEAN_encode_uper)) ::
 (_BOOLEAN_encode_oer, Gfun(Internal f_BOOLEAN_encode_oer)) ::
 (_BOOLEAN_decode_oer, Gfun(Internal f_BOOLEAN_decode_oer)) ::
 (_BOOLEAN_compare, Gfun(Internal f_BOOLEAN_compare)) ::
 (_BOOLEAN_random_fill, Gfun(Internal f_BOOLEAN_random_fill)) :: nil).

Definition public_idents : list ident :=
(_BOOLEAN_random_fill :: _BOOLEAN_compare :: _BOOLEAN_decode_oer ::
 _BOOLEAN_encode_oer :: _BOOLEAN_encode_uper :: _BOOLEAN_decode_uper ::
 _BOOLEAN_free :: _BOOLEAN_print :: _BOOLEAN_encode_xer ::
 _BOOLEAN_decode_xer :: _BOOLEAN_encode_der :: _BOOLEAN_decode_ber ::
 _asn_DEF_BOOLEAN :: _asn_OP_BOOLEAN :: _xer_decode_primitive ::
 _der_encode_primitive :: _ber_decode_primitive ::
 _ASN__PRIMITIVE_TYPE_free :: _asn_TYPE_outmost_tag ::
 _oer_encode_primitive :: _oer_decode_primitive :: _asn_random_between ::
 _asn_generic_unknown_constraint :: _asn_generic_no_constraint ::
 _asn_put_few_bits :: _asn_get_few_bits :: _xer_check_tag ::
 _der_write_tags :: _ber_check_tags :: _memset :: _free :: _calloc ::
 _malloc :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fsqrt :: ___builtin_fabs ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


