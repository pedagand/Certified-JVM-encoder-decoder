Require Import List.
Require Import String.

Inductive op_type :=
| imm_t : op_type
| reg_t : op_type.

Scheme Equality for op_type.

Inductive imediate :=
| imm : nat -> imediate.

Inductive register :=
| reg : nat -> register.

Inductive operande :=
| imm_o : imediate -> operande
| reg_o : register -> operande.

Scheme Equality for operande.

Inductive tag_op_types :=
  | ts : list op_type -> tag_op_types.

Fixpoint op_types_beq (l1 l2 : list op_type) :=
match l1, l2 with
        | h1::x1, h2::x2 => andb (op_type_beq h1 h2) (op_types_beq x1 x2)
        | nil, nil => true
        | _, _ => false
end
.

Fixpoint tag_op_types_beq (t1 t2 : tag_op_types) :=
  match t1, t2 with
    ts l1, ts l2 => op_types_beq l1 l2
  end
.

Inductive instr {T : Type} :=
| cinstr : T -> tag_op_types -> instr.
(* pour tester : créer l'ensemble des tags ici *)

Variable tag : Type.
Variable beq_T : tag -> tag -> bool.
Variable beq_T_refl : forall (t : tag), beq_T t t = true.

Definition instr_beq (T : Type) (i1 i2 : instr) :=
  match i1,i2 with
  | cinstr t1 tot1,cinstr t2 tot2 => andb (beq_T t1 t2)  (tag_op_types_beq tot1 tot2) 
  end.

Search (andb _ _ = true).

Print instr_beq.
Lemma op_type_beq_reflexivity: forall (o: op_type), op_type_beq o o = true.
Proof.
  destruct o; auto.
Qed.

Lemma op_types_beq_reflexivity: forall (o: list op_type), op_types_beq o o = true.
Proof.
  intro.
  induction o; try auto.
  - simpl. rewrite op_type_beq_reflexivity. rewrite IHo. auto.
Qed.

Lemma tag_op_types_beq_reflexivity: forall (t: tag_op_types), tag_op_types_beq t t = true.
Proof.
  destruct t.
  simpl.
  rewrite op_types_beq_reflexivity.
  reflexivity.
Qed.

Lemma instr_beq_reflexivity : forall (t : instr), instr_beq tag t t = true.
Proof.
  intro t.
  destruct t. simpl. rewrite tag_op_types_beq_reflexivity. rewrite beq_T_refl.
  auto.
Qed.



(*=tag_beq_different *)  
Lemma instr_beq_different : forall (t1 t2 : instr),
    instr_beq tag t1 t2 = true -> t1 = t2.
(*=End *)
Proof.
  intros. destruct t1. destruct t2. simpl in H. rewrite Bool.andb_true_iff in H. destruct H. rewrite tag_op_types_beq_reflexivity in H0.
  
  destruct t1; destruct t; destruct t2; destruct t; try reflexivity; try discriminate.
Qed.
  
    

(* maybe it's not usefull to distinguish the special register than the 
other because the specification says that you have different numbers for them *)

(* instruction definition *)
(*=instruction_tern_n *)
Record instruction_duo :=
  mk_instr_d { instr_opcode_t_n : tag_duo; 
             instr_operande1_t : operande ; 
             instr_operande2_t : operande }.
(*=End *)

Record instruction_uno :=
  mk_instr_u { instr_opcode_d : tag_uno; 
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


