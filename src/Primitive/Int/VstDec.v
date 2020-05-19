(* Decoding fails : 
   1) when calloc fails to allocate memory for the output structure sptr (FAIL) SEP spec
   2) if ber_check_tags return FAIL (when?) or MORE (?) - executable spec
   3) if not enough data according to length read (MORE) - executable spec
   4) expected length doesn't fit into size (FAIL) ?

        st->size = (int)length;
	/* The following better be optimized away. */
	if(sizeof(st->size) != sizeof(length)
			&& (ber_tlv_len_t)st->size != length) {
		st->size = 0;
		ASN__DECODE_FAILED;
	}

   5) malloc buf allocation fails (FAIL) SEP spec
 *)
