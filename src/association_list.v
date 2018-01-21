Require Import List Nat Arith String. 
Import ListNotations.
Require Import Mmx.ast_instructions.

  
(*=assoc *)
Definition assoc : Type :=
  tag * nat.
(*=End *)
(*=tag_opcode_assoc *)
Definition tag_opcode_assoc :=
  list assoc.
(*=End *)
Scheme Equality for list.
Check list_beq.


(* actually this is a good name for this function :p *)
(*=lookup *)
Fixpoint lookup (t : tag) (l : tag_opcode_assoc) : option nat :=
  match l with
    | [] => None
    | (t',n) :: tl => if beq_T t t'
                      then Some n
                      else lookup t tl
  end.
(*=End *)
(* actually this is a good name for this function :p *)
(*=lookdown *)
Fixpoint lookdown (n : nat) (l : tag_opcode_assoc) : option tag :=
  match l with
    | [] => None
    | (t,n') :: tl => if  eqb n n'
                      then Some t
                      else lookdown n tl
  end.
(*=End *)

(* this table is an association list of type tag_opcode_assoc with every associations that can be made in our langage *)
(*=encdec *)
Variable encdec : tag_opcode_assoc.


Require Import Bool.

Print tag.

Print reflect.

Definition propP := forall x : nat, x = x.
Check propP.
Check reflect False true.
Check ReflectT True.
Lemma test_reflect : True -> reflect True true.
Proof.
  exact (ReflectT True).
Qed.






(*=forall_tagP *)
Lemma forall_tagP: forall (P : tag -> Prop)(f : tag -> bool),
    (forall (t : tag), reflect (P t) (f t)) ->
    reflect (forall t1, P t1) (forall t', f t').
(*=End *)
Proof.
  intros P f H.
  Search reflect.
  apply iff_reflect.
  apply iff_to_and.
  split.
  -Search forall_tag.
   intros.
   apply helpBefore2.
   intros t.
   specialize (H t).
   Search forall_tag.
   Check reflect_iff.
   apply reflect_iff in H.
   inversion H.
   specialize (H0 t).
   apply H1.
   exact H0.
  -intros.
   specialize (H t).
   rewrite helpBefore1 in H.
   inversion H.
   +exact H1.
   +exact H0.
Qed.


    
SearchAbout leb.
(* the first nat is the maximum we wan't to have in this bounded nat interval *)
Fixpoint forall_bounded (n : nat) (f : nat -> bool) : bool :=
  match n with
  | 0 => f 0
  | S n => f (S n) && forall_bounded n f
  end.

Lemma help_forall_findP1 : forall (f : nat -> bool) (k : nat), (forall (n: nat), n <= k -> f n = true) -> forall_bounded k f = true.
Proof.
  intros.
  induction k.
  -apply H.
   reflexivity.
  -simpl.
   Search (_ && _ = true).
   apply andb_true_intro.
   split.
   +apply H.
    reflexivity.
   +apply IHk.
    intros n.
    specialize (H n).
    intros.
    apply H.
    Search (_ <= S _).
    apply le_S in H0.
    exact H0.
Qed.

Lemma help_forall_findP2 :
  forall (k : nat) (f : nat -> bool), forall_bounded k f = true -> (forall (n: nat), n <= k -> f n = true).
Proof.
  induction k.
  -simpl.
   intros.
   Search (_ <= 0).
   apply le_n_0_eq in H0.
   rewrite <- H0.
   exact H.
  -destruct n.
   +intros.
    apply IHk.
    simpl in H.
    Search (_ && _ = true).
    apply andb_prop in H.
    destruct H.
    exact H1.
    apply Peano.le_0_n.
   +apply andb_prop in H. 
    fold forall_bounded in H.
    destruct H.
    intros.
    change (f (S n) = true) with ((fun n => f (S n)) n = true).
    apply IHk.
    {
      assert (forall (k' : nat) (f' : nat -> bool) , f' (S k') = true -> forall_bounded k' f' = true -> forall_bounded k' (fun n0 : nat => f' (S n0)) = true).
      {
        induction k'.
        -intros.
         simpl.
         auto.
        -intros.
         simpl.
         rewrite H2.
         simpl.
         apply IHk'.
         +unfold forall_bounded in H3.
          fold forall_bounded in H3.
          apply andb_true_iff in H3.
          destruct H3.
          auto.
         +unfold forall_bounded in H3.
          fold forall_bounded in H3.
          apply andb_true_iff in H3.
          destruct H3.
          auto.
      }
      auto.       
    }
    {
      Search (S _ <= S _).
      apply le_S_n in H1.
      exact H1.
    }
Qed.
    
    

Lemma forall_finP: forall (P : nat -> Prop)(f : nat -> bool) (k : nat),
    (forall (n : nat), reflect (P n) (f n)) ->
    reflect (forall n, n <= k -> P n) (forall_bounded k f).
Proof.
  intros P f k H.
  apply iff_reflect.
  apply iff_to_and.
  split.
  -intros.
   Check help_forall_findP1.
   apply help_forall_findP1.
   intros.
   specialize (H n).
   apply reflect_iff in H.
   inversion H.
   apply H2.
   apply H0.
   exact H1.
  -intros.
   Check help_forall_findP2.
   eapply help_forall_findP2 in H0.
   specialize (H n).
   rewrite H0 in H.
   inversion H.
   exact H2.
   exact H1.
Qed.


  
  
  
(*=imply *)
Definition imply (a b : bool): bool := if a then b else true.
(*=End *)

(*=implyP *)
Lemma implyP: forall A B a b, reflect A a -> reflect B b -> reflect (A -> B) (imply a b).
(*=End *)
Proof.
  intros.
  apply reflect_iff in H.
  inversion H.
  apply reflect_iff in H0.
  inversion H0.
  apply iff_reflect.
  apply iff_to_and.
  unfold imply.
  split.  
  -intros.
   destruct a.
   +apply H3.
    apply H5.
    apply H2.
    reflexivity.
   +reflexivity. 
  -intros.
   destruct b.
   +apply H4.
    reflexivity.
   +destruct a.
    {
      discriminate.
    }
    {
      apply H4.
      apply H1.
      exact H6.
    }
Qed.

SearchAbout beq_nat.

Definition eq_mtag (t1 t2: option tag): bool :=
  match t1,t2 with
  | Some t1', Some t2' => tag_beq t1' t2'
  | _,_ => false
  end.

Lemma eq_mtag_equiv : forall (t1 t2 : option tag), eq_mtag t1 t2 = true -> t1 = t2.
Proof.
  destruct t1.
  -destruct t2.
   +simpl.
   intros.
   apply tag_beq_different in H.
   rewrite H.
   reflexivity.
   +discriminate.
  -discriminate.
Qed.


Definition eq_mnat (t1 t2: option nat): bool :=
  match t1,t2 with
  | Some n1,Some n2 => beq_nat n1 n2
  | _,_ => false
  end.

Lemma eq_mnat_equiv : forall (n1 n2 : option nat), eq_mnat n1 n2 = true -> n1 = n2.
Proof.
  destruct n1.
  -destruct n2.
   +simpl.
    intros.
    Search (_ =? _ = true).
    apply beq_nat_true in H.
    rewrite H.
    reflexivity.
   +discriminate.
  -discriminate.
Qed.

Variable codemax:  nat.
  

Definition lookdown_encdec : bool :=
  forall_bounded codemax (fun n =>                     
                      forall (t:tag), imply (eq_mtag (lookdown n encdec) (Some t))
                                                 (eq_mnat (lookup t encdec) (Some n))).
(*=lookup_encdec *)
Definition lookup_encdec : bool :=
  forall_bounded codemax (fun n =>                     
             forall (t:tag),
                imply (eq_mnat (lookup t encdec) (Some n))
                      (eq_mtag (lookdown n encdec) (Some t)))).
(*=End *)

Lemma lookdown_encdec_true : lookdown_encdec = true.
Proof. vm_compute; reflexivity. Qed.

Lemma lookup_encdec_true : lookup_encdec = true.
Proof. vm_compute; reflexivity. Qed.

(*=lookdown_encdecP *)
Lemma lookdown_encdecP: 
  reflect (forall (n : nat), n <= codemax ->
            forall (t : tag),
              lookdown n encdec = Some t ->
              lookup t encdec = Some n)
          lookdown_encdec.
Proof.
unfold lookdown_encdec.
apply forall_finP.        
intro n.
apply forall_tagP.
intros t.
apply implyP.
- assert (reflect (lookdown n encdec = Some t) (eq_mtag (lookdown n encdec) (Some t))).
  {
    apply iff_reflect.
    apply iff_to_and.
    split.
    +intros.
     rewrite H.
     simpl.
     rewrite tag_beq_reflexivity.
     reflexivity.
    +intros.
     apply eq_mtag_equiv in H.
     exact H.       
  }
  exact H.
-assert (reflect (lookup t encdec = Some n) (eq_mnat (lookup t encdec) (Some n))).
 {
   apply iff_reflect.
   apply iff_to_and.
   split.
   -intros.
    rewrite H.
    simpl.
    Search (_ =? _).
    rewrite <- beq_nat_refl.
    reflexivity.
   -intros.
    apply eq_mnat_equiv in H.
    exact H.
 }
 exact H.
Qed.

(*=lookdown_lookup *)
Theorem lookdown_lookup : forall (n : nat) (t : tag),
    lookdown n encdec = Some t -> lookup t encdec = Some n.
(*=End *)
Proof.
  (* i admit this only because computing is too long *)
  assert (H': lookdown_encdec = true) by apply lookdown_encdec_true.
  pose proof lookdown_encdecP.
  rewrite H' in H.
  inversion H.
  intros n.
  Search (_ <= _ \/ _).
  Check Nat.le_gt_cases.
  specialize (Nat.le_gt_cases n codemax).
  intros.
  destruct H1.
  -apply H0.
   exact H1.
   exact H2.
  -assert (exists m, n = codemax + m + 1)
      by (eexists; eapply le_plus_minus; eauto).
   destruct H3.
   subst n.
   simpl in H2.
   discriminate.
Qed.


(* need to find how to refactor the proof *)
Lemma lookup_val : forall (t : tag), forall (n : nat), lookup t encdec = Some n -> n <= codemax.
Proof.
  intros. 
  destruct t ; destruct t; simpl in H; inversion H; try (repeat (apply le_n_S)); apply Peano.le_0_n.
Qed.

Definition forall_inv (t: tag)(p: nat -> bool): bool :=
                     match lookup t encdec with
                       | Some n => p n
                       | None => false end).

Lemma lookup_true : forall( t:tag), forall_inv t (fun n =>
                         n <=? codemax + 30)) = true.
Proof. try (vm_compute; reflexivity). Qed.


Theorem lookup_encdecP:
  reflect (forall (n : nat), n <= codemax ->
             forall (t : tag),
               lookup t encdec = Some n ->
               lookdown n encdec = Some t)
          lookup_encdec.
Proof.
unfold lookdown_encdec.
SearchAbout reflect.
Check forall_finP.
apply forall_finP.
Check forall_tagP.
intros n.
apply forall_tagP.
SearchAbout reflect.
Check implyP.
intros t.
apply implyP.
-assert (reflect (lookup t encdec = Some n) (eq_mnat (lookup t encdec) (Some n))).
 {
   apply iff_reflect.
   apply iff_to_and.
   split.
   +intros.
    rewrite H.
    simpl.
    apply Nat.eqb_refl.
   +intros.
    apply eq_mnat_equiv in H.
    exact H.
 }
 exact H.
    -assert (reflect (lookdown n encdec = Some t) (eq_mtag (lookdown n encdec) (Some t))).
     {
       apply iff_reflect.
       apply iff_to_and.
       split.
       +intros.
        rewrite H.
        simpl.
        apply tag_beq_reflexivity.
       +intros.
        apply eq_mtag_equiv in H.
        exact H.
     }
     exact H.
Qed.

(*=lookup_lookdown *)
Theorem lookup_lookdown : forall (n : nat) (t : tag) ,
    lookup t encdec = Some n -> lookdown n encdec = Some t.
(*=End *)
(*=lookup_lookdown_script *)
Proof.
  pose proof lookup_encdecP.
  assert (lookup_encdec = true) by apply lookup_encdec_true.
  rewrite H0 in H.
  inversion H.
  intros n.
  specialize (Nat.le_gt_cases n 226).
  intros.
  destruct H2.
  -apply H1.
   exact H2.
   exact H3.
  - pose proof lookup_val t n H3.
    now apply lt_not_le in H4.
Qed.
(*=End *)


