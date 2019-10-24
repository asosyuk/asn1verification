Require Import StructTact.StructTactics.
Require Import Core.Core Core.Notations Core.Tactics Core.PtrLemmas.
Require Import Automaton Spec.

Notation option_lift := RingMicromega.map_option.

Definition string := list byte.

(** * Memory read *)
(* read [n] consecutive bytes from memory [m] starting at addres [a] *)
Definition bytes_of_mem (m : mem) (a : addr) (n : Z) : option (string) :=
  let '(b, ofs) := a in
  (option_lift proj_bytes) (Mem.loadbytes m b (Ptrofs.unsigned ofs) n).

Definition bytes_between (m : mem) (a1 a2 : addr) : option (string) :=
  match distance m a1 a2 with
  | Some n => bytes_of_mem m a1 (Z.of_nat n + 1%Z)
  | None => None
  end.

Definition plus_byte := Byte.repr 43.
Definition minus_byte := Byte.repr 45.
Definition zero_byte := Byte.repr 48.
Definition nine_byte := Byte.repr 57.

Definition char_of_byte (b : byte) : char :=
  if (b == plus_byte)%byte
  then sign_char true
  else if (b == minus_byte)%byte
       then sign_char false
       else if ((zero_byte <= b) && (b <= nine_byte))%byte
            then digit_char (Z.to_nat (Byte.signed (b - zero_byte)%byte))
            else other_char.

Definition chars_between (m : mem) (a1 a2 : addr) : option (list char) :=
  option_map (map char_of_byte) (bytes_between m a1 a2).

Definition result_of_state (s : strtoimax_state) :=
  match s with
  | EMPTY =>         ASN_STRTOX_ERROR_INVAL
  | INVAL =>         ASN_STRTOX_ERROR_INVAL
  | MORE _ =>        ASN_STRTOX_EXPECT_MORE
  | OK _ _ _ =>      ASN_STRTOX_OK
  | OK_MAX =>        ASN_STRTOX_OK
  | RANGE =>         ASN_STRTOX_ERROR_RANGE
  | EXTRA =>         ASN_STRTOX_EXTRA_DATA
  end.
    
Theorem abstract_exec_equiv :
  forall chars blen m str fin intp fb fo  res res_state,
    
    load_addr Mptr m fin = Some (Vptr fb fo) ->
    chars_between m str (fb, fo) = Some chars ->
    asn_strtoimax_lim m str fin intp = Some res ->
    
    fsa_run (strtoimax_fsa blen) chars res_state ->
    
    result_of_state res_state = return_type res.
Proof.
  induction chars;
  intros until res_state;
  intros FIN CHARS EXEC FSA.
  - (* nil case *)
    inversion FSA.
  - inversion FSA.
    + inversion H2.
      * (* since a is other char EXEC will output INVAL - in corrected version *)
        admit.
      * (* since char is nil and a is sign_char *)
        admit.
      * admit.
      * admit.
   + Admitted.
(*unfold asn_strtoimax_lim in EXEC.
  repeat break_match; try discriminate; subst.
   (* INVAL case *)
  - exfalso.
    inversion FIN; subst; clear FIN.
    unfold chars_between, bytes_between, bytes_of_mem, option_map in CHARS.
    repeat break_match; try discriminate.
    unfold distance in Heqo2;
      repeat break_match; try discriminate.
    subst.
    
    (* Heqo0 + Heqo3: (fb, fo) = (b, i) *)
    (* Heqo2: n = 0 *)
    (* Heqo1: s = [c1] *)
    (* CHARS: chars = [c2] *)
    (* FSA: res_state = OK | MORE | INVAL *)

    (** ** UNPROVABLE? *****)
    admit.
  - admit.
  - admit.
  - admit.
Admitted. *)
