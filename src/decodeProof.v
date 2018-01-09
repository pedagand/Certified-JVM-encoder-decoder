Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encode.

(* weird it is not in the santard librairie *)
Lemma delete_concat : forall (b : bool) (l1 l2 : list bool), l1 = l2 -> b :: l1 = b :: l2.
Proof.  
  intros.
  destruct b.
  -rewrite H.
   reflexivity.
  -rewrite H.
   reflexivity.
Qed.


(* two obvious Lemma but very usefull during the proof *)
Lemma get_first_n_bit_0_nil : forall (bi : list bool),
    get_first_n_bit bi 0 = ([],bi).
Proof.
  destruct bi.
  -reflexivity.
  -reflexivity.
Qed.


Lemma get_first_n_bit_rewrite : forall  (n : nat) (bi : list bool), get_first_n_bit bi n = (fst(get_first_n_bit bi n),snd(get_first_n_bit bi n)).
Proof.
  Check surjective_pairing.
  intros n bi.
  specialize (surjective_pairing (get_first_n_bit bi n)).
  auto.
Qed.






(* Some lemma to make the connection between get_first_n_bit and the functions firstn and skipn *)
Lemma get_first_n_bit_firstn : forall (n : nat) (l l1 l2 : list bool), get_first_n_bit l n = (l1,l2) -> firstn n l = l1.
Proof.
  induction n.
  -intros.
   simpl.
   rewrite get_first_n_bit_0_nil in H.
   inversion H.
   reflexivity.
  -intros.
   destruct l.
   +simpl in H.
    inversion H.
    reflexivity.
   +simpl.
    simpl in H.
    rewrite get_first_n_bit_rewrite in H.
    inversion H.
    apply delete_concat.
    specialize (IHn l (fst (get_first_n_bit l n)) l2).
    apply IHn.
    rewrite <- H2.
    rewrite <- get_first_n_bit_rewrite.
    reflexivity.
Qed.


Lemma get_first_n_bit_skipn : forall (n : nat) (l l1 l2 : list bool), get_first_n_bit l n = (l1,l2) -> skipn n l = l2.
Proof.
  induction n.
  -intros.
   rewrite get_first_n_bit_0_nil in H.
   inversion H.
   reflexivity.
  -intros.
   destruct l.
   +inversion H.
    reflexivity.
   +simpl in H.
    rewrite get_first_n_bit_rewrite in H.
    inversion H.
    rewrite H2.
    simpl.
    specialize (IHn l (fst (get_first_n_bit l n)) l2).
    apply IHn.
    rewrite <- H2.
    rewrite <- get_first_n_bit_rewrite.
    reflexivity.
Qed.





Lemma get_first_n_bit_rewrite_apply : forall  (n : nat) (bi l1 l2: list bool) (a : bool),
    (a :: fst(get_first_n_bit bi n),snd(get_first_n_bit bi n)) = (l1,l2) ->
    (fst(get_first_n_bit (a :: bi) (S n)), snd(get_first_n_bit (a :: bi) (S n))) = (l1,l2).
Proof.
  intros.
  simpl.
  rewrite get_first_n_bit_rewrite.
  simpl.
  exact H.
Qed.


Lemma get_first_n_bit_res_n : forall (n : nat) (l l1 l2 : list bool), get_first_n_bit l n = (l1, l2) -> l = l1 ++ l2.
Proof.
  intros.
  assert (keep : get_first_n_bit l n = (l1, l2)) by auto.
  apply get_first_n_bit_firstn in H.
  apply get_first_n_bit_skipn in keep.
  rewrite <- H.
  rewrite <- keep.
  rewrite firstn_skipn.
  reflexivity.
Qed.



(* Lemma get_first_n_bit_rewrite  *)
Lemma help_get_first_n_bit_size_out1 : forall (bi : list bool) (n : nat) (l l0 : list bool),
    n <= length bi -> get_first_n_bit bi n = (l, l0) -> length l = n.
Proof.
  induction bi.
  -intros.
   simpl in H.
   apply le_n_0_eq in H.
   assert (forall (n' : nat), get_first_n_bit [] n' = ([],[])).
   {
     destruct n'.
     -reflexivity.
     -reflexivity.
   }
   rewrite H1 in H0.
   inversion H0.
   rewrite <- H.
   simpl.
   reflexivity.
  -intros.
   destruct n.
   +simpl in H0.
    inversion H0.
    reflexivity.
   +simpl in H.    
    apply le_S_n in H.
    simpl in H0.
    destruct l.
    {
      specialize (IHbi n [] l0).
      apply IHbi in H.
      -simpl in H.
      rewrite <- H in H0.
      rewrite get_first_n_bit_0_nil in H0.
      discriminate.
      -assert((let (l1, l2) := get_first_n_bit bi n in (a :: l1, l2)) = ([],l0) -> get_first_n_bit bi n = ([], l0)).
       {
         rewrite get_first_n_bit_rewrite in H0.
         inversion H0.         
       }
       apply H1.
       exact H0.
    }
    {
      simpl.
      apply eq_S.
      specialize (IHbi n l l0).
      apply IHbi.
      -auto.
      -rewrite get_first_n_bit_rewrite in H0.
       inversion H0.
       rewrite <- get_first_n_bit_rewrite.
       reflexivity.
    }
Qed.


Lemma get_first_n_bit_size_nil_n_opposite : forall (n : nat) (l : list bool), n <= length l -> get_first_n_bit l n = (l, []) -> length l = n.
Proof.
  induction n.
  -destruct l.
   +reflexivity.
   +discriminate.
  -intros.
   destruct l.
   +simpl in H.
    inversion H.
   +simpl in H.
    apply le_S_n in H.
    simpl.
    apply eq_S.
    apply IHn.
    { auto. }
    simpl in H0.
    rewrite get_first_n_bit_rewrite in H0.
    inversion H0.
    rewrite H2.
    rewrite H2 in H3.
    rewrite H3.
    rewrite get_first_n_bit_rewrite.
    rewrite H2.
    rewrite H3.
    reflexivity.
Qed.



Lemma help_get_first_n_bit_size_out2 : forall (bi : list bool) (n : nat) (l l0 : list bool),
    n <= length bi -> get_first_n_bit bi n = (l, l0) -> length l0 = (length bi) - n.
Proof.
  intros.
  Check get_first_n_bit_firstn.
  assert (keep : get_first_n_bit bi n = (l, l0)) by auto.
  assert (keep2 : get_first_n_bit bi n = (l, l0)) by auto.
(*   apply get_first_n_bit_firstn in H0. *)
  apply get_first_n_bit_skipn in keep.
  apply get_first_n_bit_res_n in keep2.
  rewrite keep2.
  Search (length (_ ++ _)).
  rewrite app_length.
  apply help_get_first_n_bit_size_out1 in H0.
  -Check firstn_length.
   rewrite H0.
   Search (_ - _ ).
   rewrite Nat.add_comm.
   Check Nat.sub_diag.
   Search (_ + _ - _).
   rewrite Nat.add_sub.
   reflexivity.
  -auto.
Qed.
  
  

    
Lemma get_first_n_bit_size_out : forall (n : nat) (bi l l0 : list bool),
    n <= length bi -> get_first_n_bit bi n = (l, l0) -> length l = n /\ length l0 = (length bi) - n.
Proof.
  intros.
  split.  
  -specialize (help_get_first_n_bit_size_out1 bi n l l0).
   intros.
   auto.
  -specialize (help_get_first_n_bit_size_out2 bi n l l0).
   intros.
   auto.
Qed.

Definition lolliste := [true;true;true;false;false].
Compute get_first_n_bit lolliste 1.

   
   



(* Some littles macro *)

Lemma get_first_n_bit_res_16 : forall (l l1 l2 : list bool), get_first_n_bit l 16 = (l1, l2) -> l = l1 ++ l2.
Proof.
  apply get_first_n_bit_res_n.
Qed.
Lemma get_first_n_bit_res_8 : forall (l l1 l2 : list bool), get_first_n_bit l 8 = (l1, l2) -> l = l1 ++ l2.
Proof.
  apply get_first_n_bit_res_n.
Qed.
  




     

   
   
    
  
(*=decode_encode *)
Lemma decode_encode : forall (bi : binary_instruction)
                             (i : instruction),
    decode bi = Some i -> encode i = Some bi.
(*=End *)
Proof.
  intro.
  intro.
  assert (prop : decode bi = Some i -> length bi = 32).
  {
    intros.
    unfold decode in H.
    destruct (length bi =? 32) eqn:H1.
    Search (_ =? _ = true).
    apply beq_nat_true in H1.
    rewrite H1.
    reflexivity.
    discriminate.
  }
  intro H0.
  assert (H : length bi = 32).
  {
    apply prop in H0.
    auto.
  } 
  unfold decode in H0.
  (* c'est quoi la façon de détruire (let (li, next) := get_first_n_bit bi 8 in mais en laissant en hypothèse (li, next) = get_first_n_bit bi 8 in *)
  destruct (get_first_n_bit bi 8) eqn:Hl1.
  destruct (length bi =? 32) eqn:Hl0.
  {
    Search bind.
    apply bind_rewrite in H0.
    destruct H0.
    destruct H0.
    destruct (get_first_n_bit l0 8) eqn:Hl2.
    destruct x.
    
    (* case instruction t_n *)
    -destruct (get_first_n_bit l2 8) eqn:Hl3.
     destruct (get_first_n_bit l4 8) eqn:Hl4.
     rewrite  ret_rewrite in H0.
     destruct l6.
     unfold encode.
     (* inversion H0. *)
     unfold encode_t_n.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     inversion H0.
     assert (instr_opcode_t_n
               {|
                 instr_opcode_t_n := t;
                 instr_operande1_t_n := reg (bit_n l1);
                 instr_operande2_t_n := reg (bit_n l3);
                 instr_operande3_t_n := reg (bit_n l5) |} = t) by reflexivity.
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H5.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H8.
        simpl in H8.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H7; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H10.
        simpl in H10.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H12.
         rewrite H7.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H9; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l4 = 8).
     {
       apply get_first_n_bit_size_out in Hl3.
       destruct Hl3.
       rewrite H12.
       rewrite H9.
       reflexivity.
       exact H10.
     }
     assert (8 <= length l4) by (rewrite H11; repeat apply le_n_S; apply Peano.le_0_n).
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H13.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H14.
     assert (instr_operande1_t_n
               {|
                 instr_opcode_t_n := t;
                 instr_operande1_t_n := reg (bit_n l1);
                 instr_operande2_t_n := reg (bit_n l3);
                 instr_operande3_t_n := reg (bit_n l5) |} = reg (bit_n l1)) by reflexivity.
     rewrite H15.
     Search operand_to_bin.
     assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H16.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H17.
     assert (instr_operande2_t_n
               {|
                 instr_opcode_t_n := t;
                 instr_operande1_t_n := reg (bit_n l1);
                 instr_operande2_t_n := reg (bit_n l3);
                 instr_operande3_t_n := reg (bit_n l5) |} = reg (bit_n l3)) by reflexivity.
     rewrite H18.
     assert (operand_to_bin (reg_o (reg (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -auto.
     }   
     rewrite H19.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H20.
     assert (instr_operande3_t_n
               {|
                 instr_opcode_t_n := t;
                 instr_operande1_t_n := reg (bit_n l1);
                 instr_operande2_t_n := reg (bit_n l3);
                 instr_operande3_t_n := reg (bit_n l5) |} = reg (bit_n l5)) by reflexivity.
     rewrite H21.
     assert (operand_to_bin (reg_o (reg (bit_n l5))) = Some l5).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl4.
       destruct Hl4.
       auto.
       auto.
     }   
     rewrite H22.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l5) f = f l5) by reflexivity.
     rewrite H23.
     assert (bi = (l ++ l1 ++ l3 ++ l5 ++ [])). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_8 in Hl3.
       apply get_first_n_bit_res_8 in Hl4.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite Hl4.
       reflexivity.
     }
     (* assert (length l6 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl4. *)
     (*   -destruct Hl4. *)
     (*    rewrite H26. rewrite H11. reflexivity. *)
     (*   -auto.            *)
     (* } *)
     rewrite H24.
     rewrite ret_rewrite.
     Search (_ ++ []).
     rewrite app_nil_r.
     reflexivity.
     discriminate.

     
    (* case instruction t_i *)
    -destruct (get_first_n_bit l2 8) eqn:Hl3.
     destruct (get_first_n_bit l4 8) eqn:Hl4.
     destruct l6.
     rewrite  ret_rewrite in H0.
     unfold encode.
     (* inversion H0. *)
     unfold encode_t_n.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_t_i.
     assert (instr_opcode_t_i
               {|
                 instr_opcode_t_i := t;
                 instr_operande1_t_i := reg (bit_n l1);
                 instr_operande2_t_i := reg (bit_n l3);
                 instr_operande3_t_i := imm (bit_n l5) |} = t) by reflexivity.
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H4.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H9.
        simpl in H9.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H11.
         rewrite H6.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l4 = 8).
     {
       apply get_first_n_bit_size_out in Hl3.
       destruct Hl3.
       rewrite H11.
       rewrite H8.
       reflexivity.
       exact H9.
     }
     assert (8 <= length l4) by (rewrite H10; repeat apply le_n_S; apply Peano.le_0_n).
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H12.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H13.
     assert (instr_operande1_t_i
               {|
                 instr_opcode_t_i := t;
                 instr_operande1_t_i := reg (bit_n l1);
                 instr_operande2_t_i := reg (bit_n l3);
                 instr_operande3_t_i := imm (bit_n l5) |} = reg (bit_n l1)) by reflexivity.
     rewrite H14.
     Search operand_to_bin.
     assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H15.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H16.
     assert (instr_operande2_t_i
               {|
                 instr_opcode_t_i := t;
                 instr_operande1_t_i := reg (bit_n l1);
                 instr_operande2_t_i := reg (bit_n l3);
                 instr_operande3_t_i := imm (bit_n l5) |} = reg (bit_n l3)) by reflexivity.
     rewrite H17.   
     assert (operand_to_bin (reg_o (reg (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -auto.
     }   
     rewrite H18.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H19.
     assert (instr_operande3_t_i
               {|
                 instr_opcode_t_i := t;
                 instr_operande1_t_i := reg (bit_n l1);
                 instr_operande2_t_i := reg (bit_n l3);
                 instr_operande3_t_i := imm (bit_n l5) |} = imm (bit_n l5)) by reflexivity.
     rewrite H20.
     assert (operand_to_bin (imm_o (imm (bit_n l5))) = Some l5).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl4.
       destruct Hl4.
       auto.
       auto.
     }   
     rewrite H21.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l5) f = f l5) by reflexivity.
     rewrite H22.
     assert (bi = (l ++ l1 ++ l3 ++ l5 ++ [])). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_8 in Hl3.
       apply get_first_n_bit_res_8 in Hl4.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite Hl4.
       reflexivity.
     }
     (* assert (length l6 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl4. *)
     (*   -destruct Hl4. *)
     (*    rewrite H25. rewrite H10. reflexivity. *)
     (*   -auto.            *)
     (* } *)
     rewrite H23.
     rewrite ret_rewrite.
     Search (_ ++ []).
     rewrite app_nil_r.
     reflexivity.
     discriminate.

     (* case instruction t_i2 *)
    -destruct (get_first_n_bit l2 8) eqn:Hl3.
     destruct (get_first_n_bit l4 8) eqn:Hl4.
     destruct l6.
     rewrite  ret_rewrite in H0.
     unfold encode.
     (* inversion H0. *)
     unfold encode_t_i2.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_t_i.
     assert (instr_opcode_t_i2
               {|
                 instr_opcode_t_i2 := t;
                 instr_operande1_t_i2 := reg (bit_n l1);
                 instr_operande2_t_i2 := imm (bit_n l3);
                 instr_operande3_t_i2 := reg (bit_n l5) |} = t) by reflexivity.
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H4.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H9.
        simpl in H9.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H11.
         rewrite H6.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l4 = 8).
     {
       apply get_first_n_bit_size_out in Hl3.
       destruct Hl3.
       rewrite H11.
       rewrite H8.
       reflexivity.
       exact H9.
     }
     assert (8 <= length l4) by (rewrite H10; repeat apply le_n_S; apply Peano.le_0_n).
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H12.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H13.
     assert (instr_operande1_t_i2
               {|
                 instr_opcode_t_i2 := t;
                 instr_operande1_t_i2 := reg (bit_n l1);
                 instr_operande2_t_i2 := imm (bit_n l3);
                 instr_operande3_t_i2 := reg (bit_n l5) |} = reg (bit_n l1)) by reflexivity.
     rewrite H14.
     Search operand_to_bin.
     assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H15.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H16.
     assert (instr_operande2_t_i2
               {|
                 instr_opcode_t_i2 := t;
                 instr_operande1_t_i2 := reg (bit_n l1);
                 instr_operande2_t_i2 := imm (bit_n l3);
                 instr_operande3_t_i2 := reg (bit_n l5) |} = imm (bit_n l3)) by reflexivity.
     rewrite H17.   
     assert (operand_to_bin (imm_o (imm (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -auto.
     }   
     rewrite H18.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H19.
     assert (instr_operande3_t_i2
               {|
                 instr_opcode_t_i2 := t;
                 instr_operande1_t_i2 := reg (bit_n l1);
                 instr_operande2_t_i2 := imm (bit_n l3);
                 instr_operande3_t_i2 := reg (bit_n l5) |} = reg (bit_n l5)) by reflexivity.
     rewrite H20.
     assert (operand_to_bin (reg_o (reg (bit_n l5))) = Some l5).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl4.
       destruct Hl4.
       auto.
       auto.
     }   
     rewrite H21.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l5) f = f l5) by reflexivity.
     rewrite H22.
     assert (bi = (l ++ l1 ++ l3 ++ l5 ++ [])). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_8 in Hl3.
       apply get_first_n_bit_res_8 in Hl4.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite Hl4.
       reflexivity.
     }
     (* assert (length l6 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl4. *)
     (*   -destruct Hl4. *)
     (*    rewrite H25. rewrite H10. reflexivity. *)
     (*   -auto.            *)
     (* } *)
     rewrite H23.
     rewrite ret_rewrite.
     Search (_ ++ []).
     rewrite app_nil_r.
     reflexivity.
     discriminate.


     
     (* case instruction t_i3 *)
    -destruct (get_first_n_bit l2 8) eqn:Hl3.
     destruct (get_first_n_bit l4 8) eqn:Hl4.
     destruct l6.
     rewrite  ret_rewrite in H0.
     unfold encode.
     (* inversion H0. *)
     unfold encode_t_i2.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_t_i3.
     assert (instr_opcode_t_i3
               {|
                 instr_opcode_t_i3 := t;
                 instr_operande1_t_i3 := imm (bit_n l1);
                 instr_operande2_t_i3 := reg (bit_n l3);
                 instr_operande3_t_i3 := reg (bit_n l5) |} = t) by reflexivity.
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H4.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H9.
        simpl in H9.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H11.
         rewrite H6.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l4 = 8).
     {
       apply get_first_n_bit_size_out in Hl3.
       destruct Hl3.
       rewrite H11.
       rewrite H8.
       reflexivity.
       exact H9.
     }
     assert (8 <= length l4) by (rewrite H10; repeat apply le_n_S; apply Peano.le_0_n).
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H12.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H13.
     assert (instr_operande1_t_i3
               {|
                 instr_opcode_t_i3 := t;
                 instr_operande1_t_i3 := imm (bit_n l1);
                 instr_operande2_t_i3 := reg (bit_n l3);
                 instr_operande3_t_i3 := reg (bit_n l5) |} = imm (bit_n l1)) by reflexivity.
     rewrite H14.
     Search operand_to_bin.
     assert (operand_to_bin (imm_o (imm (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H15.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H16.
     assert (instr_operande2_t_i3
               {|
                 instr_opcode_t_i3 := t;
                 instr_operande1_t_i3 := imm (bit_n l1);
                 instr_operande2_t_i3 := reg (bit_n l3);
                 instr_operande3_t_i3 := reg (bit_n l5) |} = reg (bit_n l3)) by reflexivity.
     rewrite H17.   
     assert (operand_to_bin (reg_o (reg (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -auto.
     }   
     rewrite H18.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H19.
     assert (instr_operande3_t_i3
               {|
                 instr_opcode_t_i3 := t;
                 instr_operande1_t_i3 := imm (bit_n l1);
                 instr_operande2_t_i3 := reg (bit_n l3);
                 instr_operande3_t_i3 := reg (bit_n l5) |} = reg (bit_n l5)) by reflexivity.
     rewrite H20.
     assert (operand_to_bin (reg_o (reg (bit_n l5))) = Some l5).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl4.
       destruct Hl4.
       auto.
       auto.
     }   
     rewrite H21.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l5) f = f l5) by reflexivity.
     rewrite H22.
     assert (bi = (l ++ l1 ++ l3 ++ l5 ++ [])). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_8 in Hl3.
       apply get_first_n_bit_res_8 in Hl4.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite Hl4.
       reflexivity.
     }
     (* assert (length l6 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl4. *)
     (*   -destruct Hl4. *)
     (*    rewrite H25. rewrite H10. reflexivity. *)
     (*   -auto.            *)
     (* } *)
     rewrite H23.
     rewrite ret_rewrite.
     Search (_ ++ []).
     rewrite app_nil_r.
     reflexivity.
     discriminate.


     
     (* case instruction t_i4 *)
    -destruct (get_first_n_bit l2 8) eqn:Hl3.
     destruct (get_first_n_bit l4 8) eqn:Hl4.
     destruct l6.
     rewrite  ret_rewrite in H0.
     unfold encode.
     (* inversion H0. *)
     unfold encode_t_i2.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_t_i4.
     assert (instr_opcode_t_i4
               {|
                 instr_opcode_t_i4 := t;
                 instr_operande1_t_i4 := reg (bit_n l1);
                 instr_operande2_t_i4 := imm (bit_n l3);
                 instr_operande3_t_i4 := imm (bit_n l5) |} = t) by reflexivity.
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H4.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H9.
        simpl in H9.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H11.
         rewrite H6.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l4 = 8).
     {
       apply get_first_n_bit_size_out in Hl3.
       destruct Hl3.
       rewrite H11.
       rewrite H8.
       reflexivity.
       exact H9.
     }
     assert (8 <= length l4) by (rewrite H10; repeat apply le_n_S; apply Peano.le_0_n).
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H12.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H13.
     assert (instr_operande1_t_i4
               {|
                 instr_opcode_t_i4 := t;
                 instr_operande1_t_i4 := reg (bit_n l1);
                 instr_operande2_t_i4 := imm (bit_n l3);
                 instr_operande3_t_i4 := imm (bit_n l5) |} = reg (bit_n l1)) by reflexivity.
     rewrite H14.
     Search operand_to_bin.
     assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H15.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H16.
     assert (instr_operande2_t_i4
               {|
                 instr_opcode_t_i4 := t;
                 instr_operande1_t_i4 := reg (bit_n l1);
                 instr_operande2_t_i4 := imm (bit_n l3);
                 instr_operande3_t_i4 := imm (bit_n l5) |} = imm (bit_n l3)) by reflexivity.
     rewrite H17.   
     assert (operand_to_bin (imm_o (imm (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -auto.
     }   
     rewrite H18.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H19.
     assert (instr_operande3_t_i4
               {|
                 instr_opcode_t_i4 := t;
                 instr_operande1_t_i4 := reg (bit_n l1);
                 instr_operande2_t_i4 := imm (bit_n l3);
                 instr_operande3_t_i4 := imm (bit_n l5) |} = imm (bit_n l5)) by reflexivity.
     rewrite H20.
     assert (operand_to_bin (imm_o (imm (bit_n l5))) = Some l5).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl4.
       destruct Hl4.
       auto.
       auto.
     }   
     rewrite H21.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l5) f = f l5) by reflexivity.
     rewrite H22.
     assert (bi = (l ++ l1 ++ l3 ++ l5 ++ [])). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_8 in Hl3.
       apply get_first_n_bit_res_8 in Hl4.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite Hl4.
       reflexivity.
     }
     (* assert (length l6 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl4. *)
     (*   -destruct Hl4. *)
     (*    rewrite H25. rewrite H10. reflexivity. *)
     (*   -auto.            *)
     (* } *)
     rewrite H23.
     rewrite ret_rewrite.
     Search (_ ++ []).
     rewrite app_nil_r.
     reflexivity.
     discriminate.



    (* case instruction t_i5 *)
    -destruct (get_first_n_bit l2 8) eqn:Hl3.
     destruct (get_first_n_bit l4 8) eqn:Hl4.
     destruct l6.
     rewrite  ret_rewrite in H0.
     unfold encode.
     (* inversion H0. *)
     unfold encode_t_i2.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_t_i5.
     assert (instr_opcode_t_i5
               {|
                 instr_opcode_t_i5 := t;
                 instr_operande1_t_i5 := imm (bit_n l1);
                 instr_operande2_t_i5 := imm (bit_n l3);
                 instr_operande3_t_i5 := imm (bit_n l5) |} = t) by reflexivity.
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H4.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H9.
        simpl in H9.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H11.
         rewrite H6.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l4 = 8).
     {
       apply get_first_n_bit_size_out in Hl3.
       destruct Hl3.
       rewrite H11.
       rewrite H8.
       reflexivity.
       exact H9.
     }
     assert (8 <= length l4) by (rewrite H10; repeat apply le_n_S; apply Peano.le_0_n).
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H12.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H13.
     assert (instr_operande1_t_i5
               {|
                 instr_opcode_t_i5 := t;
                 instr_operande1_t_i5 := imm (bit_n l1);
                 instr_operande2_t_i5 := imm (bit_n l3);
                 instr_operande3_t_i5 := imm (bit_n l5) |} = imm (bit_n l1)) by reflexivity.
     rewrite H14.
     Search operand_to_bin.
     assert (operand_to_bin (imm_o (imm (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H15.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H16.
     assert (instr_operande2_t_i5
               {|
                 instr_opcode_t_i5 := t;
                 instr_operande1_t_i5 := imm (bit_n l1);
                 instr_operande2_t_i5 := imm (bit_n l3);
                 instr_operande3_t_i5 := imm (bit_n l5) |} = imm (bit_n l3)) by reflexivity.
     rewrite H17.   
     assert (operand_to_bin (imm_o (imm (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -auto.
     }   
     rewrite H18.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H19.
     assert (instr_operande3_t_i5
               {|
                 instr_opcode_t_i5 := t;
                 instr_operande1_t_i5 := imm (bit_n l1);
                 instr_operande2_t_i5 := imm (bit_n l3);
                 instr_operande3_t_i5 := imm (bit_n l5) |} = imm (bit_n l5)) by reflexivity.
     rewrite H20.
     assert (operand_to_bin (imm_o (imm (bit_n l5))) = Some l5).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl4.
       destruct Hl4.
       auto.
       auto.
     }   
     rewrite H21.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l5) f = f l5) by reflexivity.
     rewrite H22.
     assert (bi = (l ++ l1 ++ l3 ++ l5 ++ [])). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_8 in Hl3.
       apply get_first_n_bit_res_8 in Hl4.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite Hl4.
       reflexivity.
     }
     (* assert (length l6 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl4. *)
     (*   -destruct Hl4. *)
     (*    rewrite H25. rewrite H10. reflexivity. *)
     (*   -auto.            *)
     (* } *)
     rewrite H23.
     rewrite ret_rewrite.
     Search (_ ++ []).
     rewrite app_nil_r.
     reflexivity.
     discriminate.


     
    (* case instruction t_i6 *)
    -destruct (get_first_n_bit l2 8) eqn:Hl3.
     destruct (get_first_n_bit l4 8) eqn:Hl4.
     destruct l6.
     rewrite  ret_rewrite in H0.
     unfold encode.
     (* inversion H0. *)
     unfold encode_t_i2.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_t_i6.
     assert (instr_opcode_t_i6
               {|
                 instr_opcode_t_i6 := t;
                 instr_operande1_t_i6 := imm (bit_n l1);
                 instr_operande2_t_i6 := reg (bit_n l3);
                 instr_operande3_t_i6 := imm (bit_n l5) |} = t) by reflexivity.
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H4.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H9.
        simpl in H9.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H11.
         rewrite H6.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l4 = 8).
     {
       apply get_first_n_bit_size_out in Hl3.
       destruct Hl3.
       rewrite H11.
       rewrite H8.
       reflexivity.
       exact H9.
     }
     assert (8 <= length l4) by (rewrite H10; repeat apply le_n_S; apply Peano.le_0_n).
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H12.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H13.
     assert (instr_operande1_t_i6
               {|
                 instr_opcode_t_i6 := t;
                 instr_operande1_t_i6 := imm (bit_n l1);
                 instr_operande2_t_i6 := reg (bit_n l3);
                 instr_operande3_t_i6 := imm (bit_n l5) |} = imm (bit_n l1)) by reflexivity.
     rewrite H14.
     Search operand_to_bin.
     assert (operand_to_bin (imm_o (imm (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H15.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H16.
     assert (instr_operande2_t_i6
               {|
                 instr_opcode_t_i6 := t;
                 instr_operande1_t_i6 := imm (bit_n l1);
                 instr_operande2_t_i6 := reg (bit_n l3);
                 instr_operande3_t_i6 := imm (bit_n l5) |} = reg (bit_n l3)) by reflexivity.
     rewrite H17.   
     assert (operand_to_bin (reg_o (reg (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -auto.
     }   
     rewrite H18.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H19.
     assert (instr_operande3_t_i6
               {|
                 instr_opcode_t_i6 := t;
                 instr_operande1_t_i6 := imm (bit_n l1);
                 instr_operande2_t_i6 := reg (bit_n l3);
                 instr_operande3_t_i6 := imm (bit_n l5) |} = imm (bit_n l5)) by reflexivity.
     rewrite H20.
     assert (operand_to_bin (imm_o (imm (bit_n l5))) = Some l5).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl4.
       destruct Hl4.
       auto.
       auto.
     }   
     rewrite H21.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l5) f = f l5) by reflexivity.
     rewrite H22.
     assert (bi = (l ++ l1 ++ l3 ++ l5 ++ [])). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_8 in Hl3.
       apply get_first_n_bit_res_8 in Hl4.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite Hl4.
       reflexivity.
     }
     (* assert (length l6 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl4. *)
     (*   -destruct Hl4. *)
     (*    rewrite H25. rewrite H10. reflexivity. *)
     (*   -auto.            *)
     (* } *)
     rewrite H23.
     rewrite ret_rewrite.
     Search (_ ++ []).
     rewrite app_nil_r.
     reflexivity.
     discriminate.

     
     
     
     
    (* case d_i *)
    -destruct (get_first_n_bit l2 16) eqn:Hl3.
     rewrite  ret_rewrite in H0.
     unfold encode.
     destruct l4.
     (* inversion H0. *)
     unfold encode_t_n.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_d_i.
     assert (instr_opcode_d_i
               {|
                 instr_opcode_d_i := t;
                 instr_operande1_d_i := reg (bit_n l1);
                 instr_operande2_d_i := imm (bit_n l3) |} = t) by reflexivity.   
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H4.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H9.
        simpl in H9.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H11.
         rewrite H6.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     (* assert (length l4 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl3. *)
     (*   destruct Hl3. *)
     (*   rewrite H11. *)
     (*   rewrite H8. *)
     (*   reflexivity. *)
     (*   rewrite H8. *)
     (*   reflexivity. *)
     (* } *)
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H10.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H11.
     assert (instr_operande1_d_i
               {|
                 instr_opcode_d_i := t;
                 instr_operande1_d_i := reg (bit_n l1);
                 instr_operande2_d_i := imm (bit_n l3) |} = reg (bit_n l1)) by reflexivity.
     rewrite H12.
     Search operand_to_bin.
     assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H13.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H14.
     assert (instr_operande2_d_i
               {|
                 instr_opcode_d_i := t;
                 instr_operande1_d_i := reg (bit_n l1);
                 instr_operande2_d_i := imm (bit_n l3) |} = imm (bit_n l3)) by reflexivity.
     rewrite H15.   
     assert (operand_to_bin_double (imm_o (imm (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -rewrite H8. auto.
     }   
     rewrite H16.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H17.
     assert (bi = (l ++ l1 ++ l3)). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_16 in Hl3.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite app_nil_r.
       reflexivity.
     }
     rewrite H18.
     rewrite ret_rewrite.
     reflexivity.
     discriminate.

     
    (* case d_i2 *)
    -destruct (get_first_n_bit l2 16) eqn:Hl3.
     rewrite  ret_rewrite in H0.
     unfold encode.
     destruct l4.
     (* inversion H0. *)
     unfold encode_t_n.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_d_i2.
     assert (instr_opcode_d_i2
               {|
                 instr_opcode_d_i2 := t;
                 instr_operande1_d_i2 := imm (bit_n l1);
                 instr_operande2_d_i2 := reg (bit_n l3) |} = t) by reflexivity.   
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H4.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H9.
        simpl in H9.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H11.
         rewrite H6.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     (* assert (length l4 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl3. *)
     (*   destruct Hl3. *)
     (*   rewrite H11. *)
     (*   rewrite H8. *)
     (*   reflexivity. *)
     (*   rewrite H8. *)
     (*   reflexivity. *)
     (* } *)
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H10.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H11.
     assert (instr_operande1_d_i2
               {|
                 instr_opcode_d_i2 := t;
                 instr_operande1_d_i2 := imm (bit_n l1);
                 instr_operande2_d_i2 := reg (bit_n l3) |} = imm (bit_n l1)) by reflexivity.
     rewrite H12.
     Search operand_to_bin.
     assert (operand_to_bin (imm_o (imm (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H13.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H14.
     assert (instr_operande2_d_i2
               {|
                 instr_opcode_d_i2 := t;
                 instr_operande1_d_i2 := imm (bit_n l1);
                 instr_operande2_d_i2 := reg (bit_n l3) |} = reg (bit_n l3)) by reflexivity.
     rewrite H15.   
     assert (operand_to_bin_double (reg_o (reg (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -rewrite H8. auto.
     }   
     rewrite H16.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H17.
     assert (bi = (l ++ l1 ++ l3)). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_16 in Hl3.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite app_nil_r.
       reflexivity.
     }
     rewrite H18.
     rewrite ret_rewrite.
     reflexivity.
     discriminate.

     (* case d_i3 *)
    -destruct (get_first_n_bit l2 16) eqn:Hl3.
     rewrite  ret_rewrite in H0.
     unfold encode.
     destruct l4.
     (* inversion H0. *)
     unfold encode_t_n.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_d_i3.
     assert (instr_opcode_d_i3
               {|
                 instr_opcode_d_i3 := t;
                 instr_operande1_d_i3 := imm (bit_n l1);
                 instr_operande2_d_i3 := imm (bit_n l3) |} = t) by reflexivity.   
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H4.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H9.
        simpl in H9.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H11.
         rewrite H6.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     (* assert (length l4 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl3. *)
     (*   destruct Hl3. *)
     (*   rewrite H11. *)
     (*   rewrite H8. *)
     (*   reflexivity. *)
     (*   rewrite H8. *)
     (*   reflexivity. *)
     (* } *)
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H10.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H11.
     assert (instr_operande1_d_i3
               {|
                 instr_opcode_d_i3 := t;
                 instr_operande1_d_i3 := imm (bit_n l1);
                 instr_operande2_d_i3 := imm (bit_n l3) |} = imm (bit_n l1)) by reflexivity.
     rewrite H12.
     Search operand_to_bin.
     assert (operand_to_bin (imm_o (imm (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H13.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H14.
     assert (instr_operande2_d_i3
               {|
                 instr_opcode_d_i3 := t;
                 instr_operande1_d_i3 := imm (bit_n l1);
                 instr_operande2_d_i3 := imm (bit_n l3) |} = imm (bit_n l3)) by reflexivity.
     rewrite H15.   
     assert (operand_to_bin_double (imm_o (imm (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -rewrite H8. auto.
     }   
     rewrite H16.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H17.
     assert (bi = (l ++ l1 ++ l3)). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_16 in Hl3.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite app_nil_r.
       reflexivity.
     }
     rewrite H18.
     rewrite ret_rewrite.
     reflexivity.
     discriminate.

          
    (* case d_n *)
    -destruct (get_first_n_bit l2 16) eqn:Hl3.
     rewrite  ret_rewrite in H0.
     unfold encode.
     destruct l4.
     (* inversion H0. *)
     unfold encode_t_n.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_d_n.
     assert (instr_opcode_d_n
               {|
                 instr_opcode_d_n := t;
                 instr_operande1_d_n := reg (bit_n l1);
                 instr_operande2_d_n := reg (bit_n l3) |} = t) by reflexivity.   
     rewrite H2.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H4.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H6; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l2 = 16).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H9.
        simpl in H9.
        apply get_first_n_bit_size_out in Hl2.
        +destruct Hl2.
         rewrite H11.
         rewrite H6.
         reflexivity.
        +auto.
       -auto.
     }
     assert (8 <= length l2) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     (* assert (length l4 = 0). *)
     (* { *)
     (*   apply get_first_n_bit_size_out in Hl3. *)
     (*   destruct Hl3. *)
     (*   rewrite H11. *)
     (*   rewrite H8. *)
     (*   reflexivity. *)
     (*   rewrite H8. *)
     (*   reflexivity. *)
     (* } *)
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H10.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H11.
     assert (instr_operande1_d_n
               {|
                 instr_opcode_d_n := t;
                 instr_operande1_d_n := reg (bit_n l1);
                 instr_operande2_d_n := reg (bit_n l3) |} = reg (bit_n l1)) by reflexivity.
     rewrite H12.
     Search operand_to_bin.
     assert (operand_to_bin (reg_o (reg (bit_n l1))) = Some l1).
     {
       unfold operand_to_bin.
       apply bit_n_bit.     
       apply get_first_n_bit_size_out in Hl2.
       -destruct Hl2.
        auto.
       -auto.
     }   
     rewrite H13.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l1) f = f l1) by reflexivity.
     rewrite H14.
     assert (instr_operande2_d_n
               {|
                 instr_opcode_d_n := t;
                 instr_operande1_d_n := reg (bit_n l1);
                 instr_operande2_d_n := reg (bit_n l3) |} = reg (bit_n l3)) by reflexivity.
     rewrite H15.   
     assert (operand_to_bin_double (reg_o (reg (bit_n l3))) = Some l3).
     {
       unfold operand_to_bin.
       apply bit_n_bit.
       apply get_first_n_bit_size_out in Hl3.
       -destruct Hl3.
        auto.
       -rewrite H8. auto.
     }   
     rewrite H16.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l3) f = f l3) by reflexivity.
     rewrite H17.
     assert (bi = (l ++ l1 ++ l3)). 
     {
       apply get_first_n_bit_res_8 in Hl1.
       apply get_first_n_bit_res_8 in Hl2.
       apply get_first_n_bit_res_16 in Hl3.
       rewrite Hl1.
       rewrite Hl2.
       rewrite Hl3.
       rewrite app_nil_r.
       reflexivity.
     }
     rewrite H18.
     rewrite ret_rewrite.
     reflexivity.
     discriminate.

    (* case u *)
    -assert (length l0 = 24).
     { Search (get_first_n_bit). apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1. rewrite H in H3. simpl in H3. auto.
       -rewrite H. repeat apply le_n_S. Search (0 <= _). apply Peano.le_0_n. }
     Search get_first_n_bit.
     assert (get_first_n_bit l0 24 = (l0,[])).
     { apply get_first_n_bit_size_nil_n in H2. auto. }
     rewrite H3 in H0.     
     rewrite  ret_rewrite in H0.
     unfold encode.
     (* inversion H0. *)
     unfold encode_u.
     apply commut_equal in H1.
     apply lookdown_lookup in H1.
     inversion H0.
     unfold encode_d_n.
     assert (instr_opcode_s
               {|
                 instr_opcode_s := t;
                 instr_operande := imm (bit_n l0); |} = t) by reflexivity.   
     rewrite H4.
     rewrite H1.
     assert (forall (f : nat -> option binary_instruction), bind (Some (bit_n l)) f = f (bit_n l)) by reflexivity.
     rewrite H6.
     (* these are premliminare assertion to refactor a little bit the code *)
     assert (8 <= length bi) by (rewrite H; repeat apply le_n_S; apply Peano.le_0_n).
     assert (length l0 = 24).
     {
       apply get_first_n_bit_size_out in Hl1.
       -destruct Hl1.
        rewrite H in H7.
        simpl in H7.
        auto.
       -auto.
     }
     assert (8 <= length l0) by (rewrite H8; repeat apply le_n_S; apply Peano.le_0_n).
     assert (n_bit 8 (bit_n l) = Some l).
     {
       Check get_first_n_bit_size_out.
       apply get_first_n_bit_size_out in Hl1.
       apply bit_n_bit.
       -destruct Hl1.
        auto.
       -rewrite H.
        repeat apply le_n_S.
        Search (0 <= _).
        apply Peano.le_0_n.
     }
     rewrite H10.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l) f = f l) by reflexivity.
     rewrite H11.
     assert (instr_operande
               {|
                 instr_opcode_s := t;
                 instr_operande := imm (bit_n l0); |} = imm (bit_n l0)) by reflexivity.
     rewrite H12.
     Search operand_to_bin.
     assert (n_bit 24 (bit_n l0) = Some l0).
     { apply bit_n_bit. rewrite H8. reflexivity. }
     rewrite H13.
     assert (forall (f : list bool -> option binary_instruction), bind (Some l0) f = f l0) by reflexivity.
     rewrite H14.
     assert (bi = (l ++ l0)). 
     {
       Search get_first_n_bit.
       apply get_first_n_bit_res_8 in Hl1.
       rewrite Hl1.
       reflexivity.
     }     
     rewrite H15.
     rewrite ret_rewrite.
     reflexivity.
     
  }
  
  discriminate.
Qed.
   
  
   
   
   



(* little propertie on decode lenght *)
Lemma decode_size : forall (bi : binary_instruction) (i : instruction),
    decode bi = Some i -> length bi = 32.
Proof.
    intros.
    unfold decode in H.
    destruct (length bi =? 32) eqn:Hl1.
    -Search (_ =? _ = true).
     apply beq_nat_true in Hl1.
     auto.
    -discriminate.    
Qed.
  