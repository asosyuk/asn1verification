(* Abstract specification from the standard *)
Require Import Core.Core Core.Notations.
Require Import Lists.List Psatz.
Import ListNotations.
Require Import ExecutableSpec.

(* Spec using bytes *)
Open Scope byte.

Definition all_zero : byte := 0.
Definition all_one : byte := Byte.repr (Byte.max_unsigned).

Inductive Length : list byte -> Prop :=
(* 8.1.3.4 *)
| Definite_short_form l : (0 <= l < 127)%Z -> Length [Byte.repr l]
(* 8.1.3.5 *)
| Definite_long_form l ls : (127 < l < 255)%Z -> Length (Byte.repr (Zlength ls)::ls)
(* 8.1.3.6 *)
| Indefinite_form : Length [Byte.repr 127].

Inductive Tag : list byte -> Prop :=
(* 8.1.2.2 *)
| Low_tag z : (z < 31)%Z -> Tag [Byte.repr z] (* TODO: tag_class and encoding,
                                                Need testbit to return trailing 0 within byte *)
(* 8.1.2.4 *)
| High_tag t ls :
    let t := Byte.or t (Byte.repr 31) in
    (* [1...][1...]...[0...] *)
    (forall l0, nth_error ls (length ls - 1) = Some l0 ->
           (Byte.unsigned l0 <= 127)%Z) ->
    (forall l1 m, (0 <= m < (length ls - 1))%nat -> 
             nth_error ls m = Some l1 ->
             (127 < Byte.unsigned l1)%Z)  ->
    Tag (t::ls). 

(* Incomplete for now, need smth like this:

Parameter Z_to_list_septet : Z -> list byte.

Definition set_lead_one b := Byte.or b (Byte.repr 128).
Definition set_lead_zero b := Byte.and b (Byte.repr 127).

| High_tag z t0  ts :
    (31 <= z)%Z ->
    let t0 := Byte.or t0 (Byte.repr 31) in
    let ts = Z_to_list_septet z in
    let ts' := (map set_lead_one
                    (firstn (length ts - 1) ts)) in
    let ts'' := set_lead_zero (last ts 0) in
    Tag z (t0'::ts'++[ts'']). *)

Parameter Seq_type : Set.

Definition asn_type_denot (t : asn_type) :=
  match t with
  | BOOLEAN => bool
  | INTEGER => Z
  | SEQUENCE => Seq_type
  end.

Notation "' a" := (asn_type_denot a) (at level 50).


Definition PrimitiveTag t := let t' := hd 0 t in
                             Byte.testbit t' 2 = false /\ Tag t.

Definition DefiniteLength l := l <> [Byte.repr 127] /\ Length l. 

Inductive BER : forall (type : asn_type), 'type -> list byte -> Prop :=
| False_BER t:
    PrimitiveTag t ->
    BER BOOLEAN false (t ++ [1] ++ [all_zero])
       
| True_BER t v :
    v <> all_zero ->
    PrimitiveTag t ->
    BER BOOLEAN true (t ++ [1] ++ [v]).

Lemma one_is_definite_len : DefiniteLength [1].
Proof.
  econstructor;
    [ discriminate | econstructor];
    auto.
  nia.
Qed.

Definition byte_to_bool b := if (b == 0)%byte then false else true.

Parameter seq_decoder : TYPE_descriptor -> err (list byte).

(* Definition ber_decoder td ls : err ('type td) := 
  match type td with
    | BOOLEAN => bool_prim_decoder td ls
    | INTEGER => bool_prim_decoder td ls
    | SEQUENCE => bool_prim_decoder td ls
  end. *)

Definition ber_decoder td (ls : list byte) : err ('type td).
Admitted.

Theorem decoder_correctness : forall td ls (b : 'type td), 
    ber_decoder td ls = inr b ->
    BER (type td) b ls.
Admitted.


Theorem decoder_completeness :  forall td ls (b : 'type td), 
    BER (type td) b ls ->
    ber_decoder td ls = inr b.
Admitted.

Theorem decoder_completeness_false : forall td ls, 
    type td = BOOLEAN -> 
    BER BOOLEAN false ls ->
    bool_prim_decoder td ls = inr Byte.zero.
Admitted.

Theorem decoder_completeness_true : forall td ls b, 
    type td = BOOLEAN -> 
    BER BOOLEAN true ls ->
    b <> Byte.zero ->
    bool_prim_decoder td ls = inr b.
Admitted.

Parameter int_to_byte : int -> byte.
Parameter bool_to_int : bool -> int.

Theorem roundtrip : forall td b, 
    type td = BOOLEAN -> 
    bool_prim_decoder td (bool_prim_encoder td b) 
                               = inr (int_to_byte b).
Admitted.

Definition ber_encoder td (b : 'type td) : list byte. 
Admitted.
 
Theorem encoder_correctness : forall td (b : 'type td), 
    BER (type td) b (ber_encoder td b).
Admitted.


