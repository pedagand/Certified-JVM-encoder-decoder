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


Inductive instruction {T : Type} :=
| cinstr : T -> list op_type -> instruction.
(* pour tester : créer l'ensemble des tags ici *)

(* thoses are the type and lemmas that have to be implemented by the user *)
(*
Variable tag : Type.
Variable beq_T : tag -> tag -> bool.
Variable beq_T_refl : forall (t : tag), beq_T t t = true.
Variable beq_T_rev : forall (t1 t2 : tag), beq_T t1 t2 = true <-> t1 = t2.
 *)

(* need an implementation to compile *)
Inductive tag :=
| bidon1 : tag
| bidon2 : tag
.

Definition beq_T (t1 t2 : tag) : bool :=
  match t1 with
    | bidon1 => match t2 with
                | bidon1 => true
                | bidon2 => false
                end
    | bidon2 => match t2 with
                | bidon1 => false
                | bidon2 => true
                end
  end
.

Lemma beq_T_refl : forall (t : tag), beq_T t t = true.
Proof.
  intro. case t; simpl; auto.
Qed.

Lemma beq_T_rev : forall (t1 t2 : tag), beq_T t1 t2 = true <-> t1 = t2.
Proof.
  intros. case t1; case t2; split; try auto; try discriminate.
Qed.
(* end of dummy implementation *)

Scheme Equality for list.

Definition instruction_beq (T : Type) (i1 i2 : instruction) :=
  match i1,i2 with
  | cinstr t1 tot1,cinstr t2 tot2 => andb (beq_T t1 t2)  (list_beq op_type op_type_beq tot1 tot2) 
  end.

Search (andb _ _ = true).

Print instruction_beq.
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
  induction t1.
  - induction t2.
    + auto.
    + discriminate.
  - induction t2.
    + discriminate.
    + case a, a0.
      * intro. simpl in H. apply IHt1 in H. subst. reflexivity.
      * discriminate.
      * discriminate.
      * intro. simpl in H. apply IHt1 in H. subst. reflexivity.
Qed.

Lemma instruction_beq_reflexivity : forall (t : instruction), instruction_beq tag t t = true.
Proof.
  intro t.
  destruct t. simpl. rewrite list_op_type_beq_reflexivity. rewrite beq_T_refl.
  auto.
Qed.
  
(*=tag_beq_different *)  
Lemma instruction_beq_different : forall (t1 t2 : instruction),
    instruction_beq tag t1 t2 = true -> t1=t2.
Proof.
  intros. destruct t1. destruct t2. simpl in H. rewrite Bool.andb_true_iff in H. destruct H. apply list_op_types_beq_rev in H0.
  rewrite H0. apply beq_T_rev in H.
  rewrite H. auto.
Qed.
  
(*=binary_instruction  *)
Definition binary_instruction := list bool.
(*=End *)

(* some example to test the record structure *)
(* Example my_instr := mk_instr_t_i (tag_t_i ADD_I) (reg 10) (reg 11) (imm 12). *)

(* Example first_field_instr := my_instr.(instr_opcode_t_intro).  *)

