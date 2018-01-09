Require Import List.
 
(*=tag_definition *)
Inductive tag_duo :=
| if_icmplt : tag_duo
| goto : tag_duo.


(* this is tag for instructions with the form (tag reg imm) *) 
Inductive tag_uno :=
(* floating point arithmetic *)
| bipush : tag_uno
| istore : tag_uno
| iload : tag_uno.

Inductive tag_zero :=
  (* jumps with relative adress *)
| iinc : tag_zero
| ireturn : tag_zero.

(*=tag *)
Inductive tag :=
| tag_d : tag_duo -> tag
| tag_u : tag_uno -> tag
| tag_z : tag_zero -> tag.
(*=End *)

Scheme Equality for tag.


Lemma tag_beq_reflexivity : forall (t :tag), tag_beq t t = true.
Proof.
  destruct t ; destruct t ; reflexivity.
Qed.
(*=tag_beq_different *)  
Lemma tag_beq_different : forall (t1 t2 : tag),
    tag_beq t1 t2 = true -> t1 = t2.
(*=End *)
Proof.
  intros.
  destruct t1;  destruct t; destruct t2; destruct t; try reflexivity; try discriminate.
Qed.
  
    

(* maybe it's not usefull to distinguish the special register than the 
other because the specification says that you have different numbers for them *)


Inductive  operande :=
  op : nat -> operande.


(* instruction definition *)
(*=instruction_tern_n *)
Record instruction_duo :=
  mk_instr_d { instr_opcode_t_n : tag_duo; 
             instr_operande1_t : operande ; 
             instr_operande2_t : operande }.
(*=End *)

Record instruction_uno :=
  mk_instr_u { instr_opcode_d : tag_duo; 
             instr_operande1_d : operande }.

Record instruction_zero :=
  mk_instr_z { instr_opcode_s : tag_zero }.



(*=instruction *)
Inductive instruction :=
| instr_d : instruction_duo -> instruction
| instr_u : instruction_uno -> instruction
| instr_z : instruction_zero -> instruction.

(*=End *)
(*=binary_instruction  *)
Definition binary_instruction := list bool.
(*=End *)

(* some example to test the record structure *)
(* Example my_instr := mk_instr_t_i (tag_t_i ADD_I) (reg 10) (reg 11) (imm 12). *)

(* Example first_field_instr := my_instr.(instr_opcode_t_i).  *)


