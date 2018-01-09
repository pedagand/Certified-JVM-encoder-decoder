Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encode.

(*=encode_decode_t_n *)
Lemma encode_decode_t_n : forall (i : instruction_tern_n)
                                 (bi : binary_instruction),
    encode_t_n i = Some bi -> decode bi = Some (instr_t_n i).
(*=End *)
Proof.
  (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2 ++ x3) 8 = (x0,x1 ++ x2 ++ x3)) by (apply get_first_n_bit_size_4; auto).  
  rewrite H7.
  apply commut_equal in H0.
  Check lookup_lookdown.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H8.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_t_n (instr_opcode_t_n i))) f = f (tag_t_n (instr_opcode_t_n i))) by reflexivity.
  rewrite H9.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2 ++ x3) 8 = (x1,x2 ++ x3)) by (apply get_first_n_bit_size_3; auto).
  rewrite H11.
  assert (length x2 = 8) by (apply commut_equal in H3; apply operand_to_bin_size in H3; auto).
  assert (get_first_n_bit  (x2 ++ x3) 8 = (x2,x3))by (apply commut_equal in H4; apply get_first_n_bit_size_tl; auto).
  rewrite H13.
  assert (length x3 = 8) by (apply commut_equal in H4; apply operand_to_bin_size in H4; auto).
  assert (get_first_n_bit  (x3) 8 = (x3,[])) by (apply get_first_n_bit_size_nil_n; auto).
  rewrite H15.
  rewrite ret_rewrite. 
  apply commut_equal in H2.
  apply operand_to_bin_hypothesis_reg in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_hypothesis_reg in H3.
  rewrite H3.
  apply commut_equal in H4.
  apply operand_to_bin_hypothesis_reg in H4.
  rewrite H4.  
  assert ({|
       instr_opcode_t_n := instr_opcode_t_n i;
       instr_operande1_t_n := instr_operande1_t_n i;
       instr_operande2_t_n := instr_operande2_t_n i;
       instr_operande3_t_n := instr_operande3_t_n i |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H16.
  repeat rewrite app_length.
  rewrite H5.
  rewrite H10.
  rewrite H12.
  rewrite H14.
  simpl.  
  reflexivity.
Qed.


Lemma encode_decode_t_i : forall (i : instruction_tern_i) (bi : binary_instruction),
    encode_t_i i = Some bi -> decode bi = Some (instr_t_i i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2 ++ x3) 8 = (x0,x1 ++ x2 ++ x3)) by (apply get_first_n_bit_size_4; auto).
  rewrite H7.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H8.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_t_i (instr_opcode_t_i i))) f = f (tag_t_i (instr_opcode_t_i i))) by reflexivity.
  rewrite H9.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2 ++ x3) 8 = (x1,x2 ++ x3)) by (apply get_first_n_bit_size_3; auto).
  rewrite H11.
  assert (length x2 = 8) by (apply commut_equal in H3; apply operand_to_bin_size in H3; auto).
  assert (get_first_n_bit  (x2 ++ x3) 8 = (x2,x3))by (apply commut_equal in H4; apply get_first_n_bit_size_tl; auto).
  rewrite H13.
  assert (length x3 = 8) by (apply commut_equal in H4; apply operand_to_bin_size in H4; auto).
  assert (get_first_n_bit  (x3) 8 = (x3,[])) by (apply get_first_n_bit_size_nil_n; auto).
  rewrite H15.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  apply operand_to_bin_hypothesis_reg in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_hypothesis_reg in H3.
  rewrite H3.
  apply commut_equal in H4.
  apply operand_to_bin_hypothesis_imm in H4.
  rewrite H4.
  assert ({|
       instr_opcode_t_i := instr_opcode_t_i i;
       instr_operande1_t_i := instr_operande1_t_i i;
       instr_operande2_t_i := instr_operande2_t_i i;
       instr_operande3_t_i := instr_operande3_t_i i |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H16.
  repeat rewrite app_length.
  rewrite H5.
  rewrite H10.
  rewrite H12.
  rewrite H14.
  simpl.  
  reflexivity.
Qed.


Lemma encode_decode_t_i2 : forall (i : instruction_tern_i2) (bi : binary_instruction),
    encode_t_i2 i = Some bi -> decode bi = Some (instr_t_i2 i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2 ++ x3) 8 = (x0,x1 ++ x2 ++ x3)) by (apply get_first_n_bit_size_4; auto).
  rewrite H7.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H8.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_t_i2 (instr_opcode_t_i2 i))) f = f (tag_t_i2 (instr_opcode_t_i2 i))) by reflexivity.
  rewrite H9.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2 ++ x3) 8 = (x1,x2 ++ x3)) by (apply get_first_n_bit_size_3; auto).
  rewrite H11.
  assert (length x2 = 8) by (apply commut_equal in H3; apply operand_to_bin_size in H3; auto).
  assert (get_first_n_bit  (x2 ++ x3) 8 = (x2,x3))by (apply commut_equal in H4; apply get_first_n_bit_size_tl; auto).
  rewrite H13.
  assert (length x3 = 8) by (apply commut_equal in H4; apply operand_to_bin_size in H4; auto).
  assert (get_first_n_bit  (x3) 8 = (x3,[])) by (apply get_first_n_bit_size_nil_n; auto).
  rewrite H15.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  Check operand_to_bin_hypothesis_reg.
  apply operand_to_bin_hypothesis_reg in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_hypothesis_imm in H3.
  rewrite H3.
  apply commut_equal in H4.
  apply operand_to_bin_hypothesis_reg in H4.
  rewrite H4.
  assert ({|
       instr_opcode_t_i2 := instr_opcode_t_i2 i;
       instr_operande1_t_i2 := instr_operande1_t_i2 i;
       instr_operande2_t_i2 := instr_operande2_t_i2 i;
       instr_operande3_t_i2 := instr_operande3_t_i2 i |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H16.
  repeat rewrite app_length.
  rewrite H5.
  rewrite H10.
  rewrite H12.
  rewrite H14.
  simpl.  
  reflexivity.
Qed.

Lemma encode_decode_t_i3 : forall (i : instruction_tern_i3) (bi : binary_instruction),
    encode_t_i3 i = Some bi -> decode bi = Some (instr_t_i3 i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2 ++ x3) 8 = (x0,x1 ++ x2 ++ x3)) by (apply get_first_n_bit_size_4; auto).
  rewrite H7.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H8.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_t_i3 (instr_opcode_t_i3 i))) f = f (tag_t_i3 (instr_opcode_t_i3 i))) by reflexivity.
  rewrite H9.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2 ++ x3) 8 = (x1,x2 ++ x3)) by (apply get_first_n_bit_size_3; auto).
  rewrite H11.
  assert (length x2 = 8) by (apply commut_equal in H3; apply operand_to_bin_size in H3; auto).
  assert (get_first_n_bit  (x2 ++ x3) 8 = (x2,x3))by (apply commut_equal in H4; apply get_first_n_bit_size_tl; auto).
  rewrite H13.
  assert (length x3 = 8) by (apply commut_equal in H4; apply operand_to_bin_size in H4; auto).
  assert (get_first_n_bit  (x3) 8 = (x3,[])) by (apply get_first_n_bit_size_nil_n; auto).
  rewrite H15.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  Check operand_to_bin_hypothesis_reg.
  apply operand_to_bin_hypothesis_imm in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_hypothesis_reg in H3.
  rewrite H3.
  apply commut_equal in H4.
  apply operand_to_bin_hypothesis_reg in H4.
  rewrite H4.
  assert ({|
       instr_opcode_t_i3 := instr_opcode_t_i3 i;
       instr_operande1_t_i3 := instr_operande1_t_i3 i;
       instr_operande2_t_i3 := instr_operande2_t_i3 i;
       instr_operande3_t_i3 := instr_operande3_t_i3 i |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H16.
  repeat rewrite app_length.
  rewrite H5.
  rewrite H10.
  rewrite H12.
  rewrite H14.
  simpl.  
  reflexivity.
Qed.


Lemma encode_decode_t_i4 : forall (i : instruction_tern_i4) (bi : binary_instruction),
    encode_t_i4 i = Some bi -> decode bi = Some (instr_t_i4 i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2 ++ x3) 8 = (x0,x1 ++ x2 ++ x3)) by (apply get_first_n_bit_size_4; auto).
  rewrite H7.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H8.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_t_i4 (instr_opcode_t_i4 i))) f = f (tag_t_i4 (instr_opcode_t_i4 i))) by reflexivity.
  rewrite H9.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2 ++ x3) 8 = (x1,x2 ++ x3)) by (apply get_first_n_bit_size_3; auto).
  rewrite H11.
  assert (length x2 = 8) by (apply commut_equal in H3; apply operand_to_bin_size in H3; auto).
  assert (get_first_n_bit  (x2 ++ x3) 8 = (x2,x3))by (apply commut_equal in H4; apply get_first_n_bit_size_tl; auto).
  rewrite H13.
  assert (length x3 = 8) by (apply commut_equal in H4; apply operand_to_bin_size in H4; auto).
  assert (get_first_n_bit  (x3) 8 = (x3,[])) by (apply get_first_n_bit_size_nil_n; auto).
  rewrite H15.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  Check operand_to_bin_hypothesis_reg.
  apply operand_to_bin_hypothesis_reg in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_hypothesis_imm in H3.
  rewrite H3.
  apply commut_equal in H4.
  apply operand_to_bin_hypothesis_imm in H4.
  rewrite H4.
  assert ({|
       instr_opcode_t_i4 := instr_opcode_t_i4 i;
       instr_operande1_t_i4 := instr_operande1_t_i4 i;
       instr_operande2_t_i4 := instr_operande2_t_i4 i;
       instr_operande3_t_i4 := instr_operande3_t_i4 i |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H16.
  repeat rewrite app_length.
  rewrite H5.
  rewrite H10.
  rewrite H12.
  rewrite H14.
  simpl.  
  reflexivity.
Qed.


Lemma encode_decode_t_i5 : forall (i : instruction_tern_i5) (bi : binary_instruction),
    encode_t_i5 i = Some bi -> decode bi = Some (instr_t_i5 i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2 ++ x3) 8 = (x0,x1 ++ x2 ++ x3)) by (apply get_first_n_bit_size_4; auto).
  rewrite H7.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H8.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_t_i5 (instr_opcode_t_i5 i))) f = f (tag_t_i5 (instr_opcode_t_i5 i))) by reflexivity.
  rewrite H9.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2 ++ x3) 8 = (x1,x2 ++ x3)) by (apply get_first_n_bit_size_3; auto).
  rewrite H11.
  assert (length x2 = 8) by (apply commut_equal in H3; apply operand_to_bin_size in H3; auto).
  assert (get_first_n_bit  (x2 ++ x3) 8 = (x2,x3))by (apply commut_equal in H4; apply get_first_n_bit_size_tl; auto).
  rewrite H13.
  assert (length x3 = 8) by (apply commut_equal in H4; apply operand_to_bin_size in H4; auto).
  assert (get_first_n_bit  (x3) 8 = (x3,[])) by (apply get_first_n_bit_size_nil_n; auto).
  rewrite H15.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  Check operand_to_bin_hypothesis_reg.
  apply operand_to_bin_hypothesis_imm in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_hypothesis_imm in H3.
  rewrite H3.
  apply commut_equal in H4.
  apply operand_to_bin_hypothesis_imm in H4.
  rewrite H4.
  assert ({|
       instr_opcode_t_i5 := instr_opcode_t_i5 i;
       instr_operande1_t_i5 := instr_operande1_t_i5 i;
       instr_operande2_t_i5 := instr_operande2_t_i5 i;
       instr_operande3_t_i5 := instr_operande3_t_i5 i |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H16.
  repeat rewrite app_length.
  rewrite H5.
  rewrite H10.
  rewrite H12.
  rewrite H14.
  simpl.  
  reflexivity.
Qed.


Lemma encode_decode_t_i6 : forall (i : instruction_tern_i6) (bi : binary_instruction),
    encode_t_i6 i = Some bi -> decode bi = Some (instr_t_i6 i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2 ++ x3) 8 = (x0,x1 ++ x2 ++ x3)) by (apply get_first_n_bit_size_4; auto).
  rewrite H7.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H8.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_t_i6 (instr_opcode_t_i6 i))) f = f (tag_t_i6 (instr_opcode_t_i6 i))) by reflexivity.
  rewrite H9.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2 ++ x3) 8 = (x1,x2 ++ x3)) by (apply get_first_n_bit_size_3; auto).
  rewrite H11.
  assert (length x2 = 8) by (apply commut_equal in H3; apply operand_to_bin_size in H3; auto).
  assert (get_first_n_bit  (x2 ++ x3) 8 = (x2,x3))by (apply commut_equal in H4; apply get_first_n_bit_size_tl; auto).
  rewrite H13.
  assert (length x3 = 8) by (apply commut_equal in H4; apply operand_to_bin_size in H4; auto).
  assert (get_first_n_bit  (x3) 8 = (x3,[])) by (apply get_first_n_bit_size_nil_n; auto).
  rewrite H15.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  Check operand_to_bin_hypothesis_reg.
  apply operand_to_bin_hypothesis_imm in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_hypothesis_reg in H3.
  rewrite H3.
  apply commut_equal in H4.
  apply operand_to_bin_hypothesis_imm in H4.
  rewrite H4.
  assert ({|
       instr_opcode_t_i6 := instr_opcode_t_i6 i;
       instr_operande1_t_i6 := instr_operande1_t_i6 i;
       instr_operande2_t_i6 := instr_operande2_t_i6 i;
       instr_operande3_t_i6 := instr_operande3_t_i6 i |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H16.
  repeat rewrite app_length.
  rewrite H5.
  rewrite H10.
  rewrite H12.
  rewrite H14.
  simpl.  
  reflexivity.
Qed.


Lemma encode_decode_d_n : forall (i : instruction_duo_n) (bi : binary_instruction),
    encode_d_n i = Some bi -> decode bi = Some (instr_d_n i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2) 8 = (x0,x1 ++ x2)) by (apply get_first_n_bit_size_3; auto).
  rewrite H6.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H7.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_d_n (instr_opcode_d_n i))) f = f (tag_d_n (instr_opcode_d_n i))) by reflexivity.
  rewrite H8.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2) 8 = (x1,x2)) by (apply get_first_n_bit_size_tl; auto).
  rewrite H10.
  assert (length x2 = 16) by (apply commut_equal in H3; apply operand_to_bin_double_size in H3; auto).
  assert (get_first_n_bit x2 16 = (x2,[]))by (apply commut_equal in H4; apply get_first_n_bit_size_nil_n; auto).
  rewrite H12.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  apply operand_to_bin_hypothesis_reg in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_double_hypothesis_reg in H3.
  rewrite H3.
  assert ({|
       instr_opcode_d_n := instr_opcode_d_n i;
       instr_operande1_d_n := instr_operande1_d_n i;
       instr_operande2_d_n := instr_operande2_d_n i; |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H13.
  repeat rewrite app_length.
  rewrite H4.
  rewrite H9.
  rewrite H11.
  simpl.  
  reflexivity.
Qed.


Lemma encode_decode_d_i : forall (i : instruction_duo_i) (bi : binary_instruction),
    encode_d_i i = Some bi -> decode bi = Some (instr_d_i i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2) 8 = (x0,x1 ++ x2)) by (apply get_first_n_bit_size_3; auto).
  rewrite H6.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H7.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_d_i (instr_opcode_d_i i))) f = f (tag_d_i (instr_opcode_d_i i))) by reflexivity.
  rewrite H8.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2) 8 = (x1,x2)) by (apply get_first_n_bit_size_tl; auto).
  rewrite H10.
  assert (length x2 = 16) by (apply commut_equal in H3; apply operand_to_bin_double_size in H3; auto).
  assert (get_first_n_bit x2 16 = (x2,[]))by (apply commut_equal in H4; apply get_first_n_bit_size_nil_n; auto).
  rewrite H12.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  apply operand_to_bin_hypothesis_reg in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_double_hypothesis_imm in H3.
  rewrite H3.
  assert ({|
       instr_opcode_d_i := instr_opcode_d_i i;
       instr_operande1_d_i := instr_operande1_d_i i;
       instr_operande2_d_i := instr_operande2_d_i i; |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H13.
  repeat rewrite app_length.
  rewrite H4.
  rewrite H9.
  rewrite H11.
  reflexivity.
Qed.


Lemma encode_decode_d_i2 : forall (i : instruction_duo_i2) (bi : binary_instruction),
    encode_d_i2 i = Some bi -> decode bi = Some (instr_d_n2 i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2) 8 = (x0,x1 ++ x2)) by (apply get_first_n_bit_size_3; auto).
  rewrite H6.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H7.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_d_i2 (instr_opcode_d_i2 i))) f = f (tag_d_i2 (instr_opcode_d_i2 i))) by reflexivity.
  rewrite H8.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2) 8 = (x1,x2)) by (apply get_first_n_bit_size_tl; auto).
  rewrite H10.
  assert (length x2 = 16) by (apply commut_equal in H3; apply operand_to_bin_double_size in H3; auto).
  assert (get_first_n_bit x2 16 = (x2,[]))by (apply commut_equal in H4; apply get_first_n_bit_size_nil_n; auto).
  rewrite H12.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  apply operand_to_bin_hypothesis_imm in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_double_hypothesis_reg in H3.
  rewrite H3.
  assert ({|
       instr_opcode_d_i2 := instr_opcode_d_i2 i;
       instr_operande1_d_i2 := instr_operande1_d_i2 i;
       instr_operande2_d_i2 := instr_operande2_d_i2 i; |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H13.
  repeat rewrite app_length.
  rewrite H4.
  rewrite H9.
  rewrite H11.
  reflexivity.
Qed.



Lemma encode_decode_d_i3 : forall (i : instruction_duo_i3) (bi : binary_instruction),
    encode_d_i3 i = Some bi -> decode bi = Some (instr_d_n3 i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  unfold decode.
  rewrite ret_rewrite in H.
  inversion H.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  assert (get_first_n_bit (x0 ++ x1 ++ x2) 8 = (x0,x1 ++ x2)) by (apply get_first_n_bit_size_3; auto).
  rewrite H6.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H7.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_d_i3 (instr_opcode_d_i3 i))) f = f (tag_d_i3 (instr_opcode_d_i3 i))) by reflexivity.
  rewrite H8.
  assert (length x1 = 8) by (apply commut_equal in H2; apply operand_to_bin_size in H2; auto).
  assert (get_first_n_bit  (x1 ++ x2) 8 = (x1,x2)) by (apply get_first_n_bit_size_tl; auto).
  rewrite H10.
  assert (length x2 = 16) by (apply commut_equal in H3; apply operand_to_bin_double_size in H3; auto).
  assert (get_first_n_bit x2 16 = (x2,[]))by (apply commut_equal in H4; apply get_first_n_bit_size_nil_n; auto).
  rewrite H12.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  apply operand_to_bin_hypothesis_imm in H2.
  rewrite H2.
  apply commut_equal in H3.
  apply operand_to_bin_double_hypothesis_imm in H3.
  rewrite H3.
  assert ({|
       instr_opcode_d_i3 := instr_opcode_d_i3 i;
       instr_operande1_d_i3 := instr_operande1_d_i3 i;
       instr_operande2_d_i3 := instr_operande2_d_i3 i; |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  rewrite H13.
  repeat rewrite app_length.
  rewrite H4.
  rewrite H9.
  rewrite H11.
  reflexivity.
Qed.


Lemma encode_decode_u : forall (i : instruction_uno) (bi : binary_instruction),
    encode_u i = Some bi -> decode bi = Some (instr_u i).
Proof.
    (* first part trying to get lot of information from encode_t_n *)
  intros.
  unfold encode_t_n in H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  destruct (instr_operande i) eqn:Hi.
  apply bind_rewrite in H.
  destruct H.
  destruct H.
  rewrite ret_rewrite in H.
  inversion H.
  unfold decode.
  (* now going to go further into decode *)
  assert (length x0 = 8) by (apply commut_equal in H1; apply size_n_bit in H1; auto).
  Search get_first_n_bit.
  assert (get_first_n_bit (x0 ++ x1) 8 = (x0,x1)) by (apply get_first_n_bit_size_tl; auto).
  rewrite H5.
  apply commut_equal in H0.
  apply lookup_lookdown in H0.
  apply commut_equal in H1.
  assert (bit_n x0 = x) by (apply n_bit_n in H1; exact H1).
  rewrite H6.
  rewrite H0.
  assert (forall (f : tag -> (option instruction)), bind (Some (tag_u (instr_opcode_s i))) f = f (tag_u (instr_opcode_s i))) by reflexivity.
  rewrite H7.
  assert (length x1 = 24).
  { apply commut_equal in H2. Search n_bit. apply size_n_bit in H2. auto. }
  Search (length (_ ++ _)).
  rewrite app_length.
  rewrite H8.
  rewrite H3.
  simpl.
    assert (get_first_n_bit  x1 24 = (x1,[])).
  { Search get_first_n_bit. apply get_first_n_bit_size_nil_n in H8. auto. }
  rewrite H9.
  rewrite ret_rewrite.
  apply commut_equal in H2.
  assert ({|
       instr_opcode_s := instr_opcode_s i;
       instr_operande := instr_operande i; |} = i).
  {
    simpl. destruct i.
    compute. reflexivity.
  }
  Search (n_bit).
  apply n_bit_n in H2.
  rewrite H2.
  rewrite <- Hi.
  rewrite H10.
  reflexivity.
Qed.



(*=encode_decode *)
Lemma encode_decode : forall (i : instruction) (bi : binary_instruction),
    encode i = Some bi -> decode bi = Some i.
(*=End *)
Proof.
  destruct i.
  -apply encode_decode_t_n.
  -apply encode_decode_t_i.
  -apply encode_decode_t_i2.
  -apply encode_decode_t_i3.
  -apply encode_decode_t_i4.
  -apply encode_decode_t_i5.
  -apply encode_decode_t_i6.   
  -apply encode_decode_d_n.
  -apply encode_decode_d_i.
  -apply encode_decode_d_i2.
  -apply encode_decode_d_i3.
  -apply encode_decode_u.
Qed.
  
