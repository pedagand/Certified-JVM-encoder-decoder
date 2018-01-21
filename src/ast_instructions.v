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

Inductive instr {T : Type} :=
| cinstr : T -> list op_type -> instr.
(* pour tester : créer l'ensemble des tags ici *)

Variable tag : Type.
Variable beq_T : tag -> tag -> bool.
Variable beq_T_refl : forall (t : tag), beq_T t t = true.
Variable beq_T_rev : forall (t1 t2 : tag), beq_T t1 t2 = true <-> t1 = t2.

Scheme Equality for list.

Definition instr_beq (T : Type) (i1 i2 : instr) :=
  match i1,i2 with
  | cinstr t1 tot1,cinstr t2 tot2 => andb (beq_T t1 t2)  (list_beq op_type op_type_beq tot1 tot2) 
  end.

Search (andb _ _ = true).

Print instr_beq.
Lemma op_type_beq_reflexivity: forall (o: op_type), op_type_beq o o = true.
Proof.
  destruct o; auto.
Qed.

Lemma list_op_type_beq_reflexivity: forall (o: list op_type), list_beq op_type op_type_beq o o = true.
Proof.
  intro.
  induction o; try auto.
  - simpl. rewrite op_type_beq_reflexivity. rewrite IHo. auto.
Qed.

Lemma list_op_types_beq_rev : forall (t1 t2 : list op_type), list_beq op_type op_type_beq t1 t2 = true -> t1 = t2.
Proof.
  intros.
  induction t1.
  - case t2.
    + auto.
    + intros. 
Qed.
Admitted.

Lemma instr_beq_reflexivity : forall (t : instr), instr_beq tag t t = true.
Proof.
  intro t.
  destruct t. simpl. rewrite list_op_type_beq_reflexivity. rewrite beq_T_refl.
  auto.
Qed.

Definition instr_rev: forall  (t1 t3 : tag)(t2 t4 : list op_type), instr_beq tag (cinstr t1 t2) (cinstr t3 t4)=true -> andb (beq_T t1 t3) (list_beq op_type op_type_beq t2 t4)=true.

(*=tag_beq_different *)  
Lemma instr_beq_different : forall (t1 t2 : instr),
    instr_beq tag t1 t2 = true -> t1=t2.
Proof.
  intros. destruct t1. destruct t2. simpl in H. rewrite Bool.andb_true_iff in H. destruct H. apply tag_op_types_beq_rev in H0.
  rewrite H0. apply beq_T_rev in H.
  rewrite H. auto.
Qed.
  
    

(* maybe it's not usefull to distinguish the special register than the 
other because the specification says that you have different numbers for them *)


(*=End *)
(*=binary_instruction  *)
Definition binary_instruction := list bool.
(*=End *)

(* some example to test the record structure *)
(* Example my_instr := mk_instr_t_i (tag_t_i ADD_I) (reg 10) (reg 11) (imm 12). *)

(* Example first_field_instr := my_instr.(instr_opcode_t_i).  *)


