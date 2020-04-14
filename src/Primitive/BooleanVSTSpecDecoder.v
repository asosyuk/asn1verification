Require Import Core.Core  Core.StructNormalizer VstLib Lib BooleanExecSpec ErrorWithWriter.
Require Import VST.floyd.proofauto Psatz.
Require Import VST.floyd.library.
Require Export VST.floyd.Funspec_old_Notation.

Require Import Clight.BOOLEAN BCTVSTSpec.
Require Import StructNormalizer.

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Open Scope Z.

Section Boolean_ber_decode.

Notation _asn_dec_rval_s_struct := (Tstruct _asn_dec_rval_s noattr).

Definition asn_dec_rval_rep sh v code cons :=  
 (field_at sh _asn_dec_rval_s_struct 
           [StructField _code]
           (Vint (Int.repr code)) v *
  field_at sh _asn_dec_rval_s_struct 
           [StructField _consumed] 
           (Vint (Int.repr cons)) v)%logic. 

Definition bool_ber_decode_spec : ident * funspec :=
  DECLARE _BOOLEAN_decode_ber
    WITH (* Context pointer *)
         sh_ctx : share, ctx_b : block, ctx_ofs : ptrofs, ctx : val,
         (* Type Descriptor pointer *)
         sh_td : share, td_b : block, td_ofs : ptrofs, td : TYPE_descriptor,
         (* Value double pointer *)
         sh_val: share, bool_value : val, (* pointer can be null *)
         (* Buffer pointer *)
         sh_buf : share, buf_b : block, buf_ofs : ptrofs, buf : list byte,
         (* pointer to the return struct dec_rval *)                        
         sh_res : share, res_b : block, res_ofs : ptrofs,
         size : Z, tag_mode : Z,
         bv : val, res : val,
         gv : globals
    PRE  [
         __res OF (tptr (Tstruct _asn_dec_rval_s noattr)),
         _opt_codec_ctx OF (tptr (Tstruct _asn_codec_ctx_s noattr)),
         _td OF (tptr (Tstruct _asn_TYPE_descriptor_s noattr)),
         _bool_value OF (tptr (tptr tvoid)),
         _buf_ptr OF (tptr tvoid),
         _size OF tuint,
         _tag_mode OF tint]
    PROP ( readable_share sh_ctx; 
           readable_share sh_td; 
           readable_share sh_buf;
           writable_share sh_res;
            writable_share sh_val;
           is_pointer_or_null bv
            )
    LOCAL ( temp _opt_codec_ctx ctx;
            temp _td (Vptr td_b td_ofs);
            temp _bool_value bool_value;
            temp _buf_ptr (Vptr buf_b buf_ofs);
            temp _size (Vint (Int.repr size));
            temp _tag_mode (Vint (Int.repr tag_mode));
            temp __res res)
    SEP (data_at sh_ctx (tptr (Tstruct _asn_codec_ctx_s noattr))
                   (Vptr ctx_b ctx_ofs) ctx;
         data_at sh_td (Tstruct _asn_TYPE_descriptor_s noattr)
                   (TYPE_descriptor_rep td) (Vptr td_b td_ofs);
         data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) 
                   (Vptr buf_b buf_ofs);
        data_at sh_val (tptr tvoid) bv bool_value;
        data_at_ sh_res _asn_dec_rval_s_struct res)
    POST [tvoid]
      PROP()
      LOCAL ()
      SEP( (* Unchanged by the execution : *)
           data_at sh_ctx (tptr (Tstruct _asn_codec_ctx_s noattr))
                   (Vptr ctx_b ctx_ofs) ctx;
           data_at sh_td (Tstruct _asn_TYPE_descriptor_s noattr) 
                   (TYPE_descriptor_rep td) (Vptr td_b td_ofs);
           data_at sh_buf (tarray tschar (Zlength buf)) (map Vbyte buf) 
                   (Vptr buf_b buf_ofs);
           (* Changes according to the exec spec *)
           let RC_FAIL := asn_dec_rval_rep sh_res (Vptr res_b res_ofs) 2 0 in
           if Val.eq bool_value Vnullptr 
           then RC_FAIL
           else let res := bool_decoder td buf in
           match res with
           | Some (r, c) => asn_dec_rval_rep sh_res (Vptr res_b res_ofs) 0 c * 
                            data_at sh_val (tptr tuchar) (Vbyte (bool_to_byte r)) bool_value
           | None => RC_FAIL *
                     data_at sh_val (tptr tuchar)
                             (default_val (tptr tuchar)) bool_value
           end).

Definition calloc_spec :=
   DECLARE _calloc
   WITH m : Z, n : Z, ls : list byte (*, gv : globals *)
   PRE [ 1%positive OF size_t, 2%positive OF size_t ]
       PROP (0 <= m <= Ptrofs.max_unsigned ;
             0 <= n <= Ptrofs.max_unsigned ;
             0 <= m * n <= Ptrofs.max_unsigned;
             Zlength ls = (m * n)%Z )
       LOCAL (temp 1%positive (Vptrofs (Ptrofs.repr m)); 
              temp 2%positive (Vptrofs (Ptrofs.repr n)) (*;
              gvars gv *))
       SEP ((* mem_mgr gv *))
    POST [ tptr tvoid ] EX p : val, EX t : type,
       PROP (Forall (fun x => x = Byte.zero) ls)
       LOCAL (temp ret_temp p)
       SEP ((* mem_mgr gv; *)
         if eq_dec p nullval then emp
         else (malloc_token Ews t p *
               data_at Ews (tarray tschar m) (map Vbyte ls) p)).
          
Definition Gprog2 := ltac:(with_library prog [calloc_spec; 
                                              ber_check_tags_spec; 
                                              bool_ber_decode_spec]).

Theorem bool_der_encode : semax_body Vprog Gprog2 
           (normalize_function f_BOOLEAN_decode_ber composites) bool_ber_decode_spec.
  Proof.
  start_function.
  forward.
  forward.
  forward_if True.
  entailer!.
  try autorewrite with sublist in *|-.
  eapply denote_tc_test_eq_split.
  admit.
  entailer!.
  forward_call (1, 4, [Byte.zero]). (* change spec *)
  admit.
  Intros p.
  forward.
  forward.
  forward_if.
  destruct (eq_dec (fst p) nullval) eqn : N.
  entailer!.
  admit.
  entailer!.
  repeat forward.
  entailer!.
Admitted.

End Boolean_ber_decode.
