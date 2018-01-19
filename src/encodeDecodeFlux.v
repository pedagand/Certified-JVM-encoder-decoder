Require Import Bool List Arith Nat.
Import ListNotations.
Require Import Mmx.ast_instructions Mmx.binary Mmx.association_list Mmx.encodeProof Mmx.decodeProof Mmx.encode.


(* Proof about encode_decode_flux *)
Lemma encode_decode_decoup_flux_decoup : forall (lb : list binary_instruction) (l : list instruction),
    encode_flux l = Some lb -> decode_flux_decoup lb = Some l.
Proof.
  induction lb.
  -intros.
   unfold encode_flux in H.
   assert (traverse (encode_flux_opt l) = Some [] -> l = []).
   {
     destruct l.
     -reflexivity.
     -simpl.
      destruct (encode i).
      +destruct (traverse (encode_flux_opt l)).
       discriminate.
       discriminate.
      +discriminate.
   }
   apply H0 in H.
   rewrite H.
   auto.
  -destruct l.
   +unfold encode_flux.
    simpl.
    discriminate.
   +intros.
    assert (keep : encode_flux (i :: l) = Some (a :: lb)) by auto.
    assert (encode_flux (i :: l) = Some (a :: lb) -> encode i = Some a).
    {
      unfold encode_flux.
      simpl.
      intros.
      destruct (encode i).
      assert (encode_flux (i :: l) = Some (a :: lb) -> encode_flux l = Some lb).
      {
        unfold encode_flux.
        simpl.
        intros.
        destruct (encode i).
        -destruct (traverse (encode_flux_opt l)).
         +inversion H1.
          reflexivity.
         +discriminate.
        -discriminate.
      }
      apply H1 in H.
      assert (traverse (encode_flux_opt l) = encode_flux l).
      {
        unfold encode_flux.
        reflexivity.
      }
      rewrite H2 in H0.
      rewrite H in H0.
      -inversion H0.
       reflexivity.
      -discriminate.
    }
    apply H0 in H.
    unfold decode_flux_decoup.
    simpl.
    apply encode_decode in H.
    rewrite H.
    fold decode_flux_decoup.
    assert (traverse (decode_flux_opt lb) = decode_flux_decoup lb).
    {
      unfold decode_flux_decoup.
      reflexivity.
    }
    rewrite H1.
    assert (decode_flux_decoup lb = Some l).
    {
      apply IHlb.
      assert (encode_flux (i :: l) = Some (a :: lb) -> encode_flux l = Some lb).
      {
        unfold encode_flux.
        simpl.
        intros.
        destruct (encode i).
        -destruct (traverse (encode_flux_opt l)).
         +inversion H2.
          reflexivity.
         +discriminate.
        -discriminate.
      }
      apply H2 in keep.
      auto.                   
    }
    rewrite H2.
    reflexivity.
Qed.

Lemma decode_decoup_encode_flux : forall (l : list instruction) (lb : list binary_instruction),
    decode_flux_decoup lb = Some l -> encode_flux l = Some lb.
Proof.
  induction l.
  -unfold decode_flux_decoup.
   unfold encode_flux.
   intros.
   assert (traverse (decode_flux_opt lb) = Some [] -> lb = []).
   {
     destruct lb.
     -reflexivity.
     -simpl.
      destruct (decode b).
      +destruct (traverse (decode_flux_opt lb)).
       discriminate.
       discriminate.
      +discriminate.
   }
   apply H0 in H.
   rewrite H.
   reflexivity.
  -intros.
   destruct lb.
   +unfold decode_flux_decoup in H.
    simpl in H.
    discriminate.
   +assert (keep : decode_flux_decoup (b :: lb) = Some (a :: l)) by auto.
    assert (keep2 : decode_flux_decoup (b :: lb) = Some (a :: l)) by auto.
    assert (decode_flux_decoup (b :: lb) = Some (a :: l) -> decode_flux_decoup lb = Some l).
    {
      unfold decode_flux_decoup.
      intros.
      simpl in H0.
      destruct (decode b).
      -destruct (traverse (decode_flux_opt lb)).
       +inversion H0.
        reflexivity.
       +discriminate.
      -discriminate.
    }
    apply H0 in H.
    unfold encode_flux.
    simpl.
    assert (decode_flux_decoup (b :: lb) = Some (a :: l) -> decode b = Some a).
    { 
      intros.
      unfold decode_flux_decoup in H1.
      simpl in H1.
      destruct (decode b).
      -destruct (traverse (decode_flux_opt lb)).
       +inversion H1.
       reflexivity.
       +discriminate.
      -discriminate.
    }
    apply H1 in keep.
    Search decode.
    apply decode_encode in keep.
    {
      rewrite keep.
      assert (traverse (encode_flux_opt l) = encode_flux l).
      {
        unfold encode_flux.
        reflexivity.
      }
      rewrite H2.
      assert (encode_flux l = Some lb).
      {
        apply IHl.
        auto.        
      }
      rewrite H3.
      reflexivity.
    }
Qed.    
    

(* Some proofs about cut32 and concatlistes *)

(* good proofs *)  
Lemma app_cut32 : forall (l1 l2 : list bool) (ll : list (list bool)), length l1 = 32 -> cut32 l2 = Some ll
                                                                      -> cut32 (l1 ++ l2) = Some (l1 :: ll).
Proof.
  intros.
  unfold cut32.
  assert (length (l1 ++ l2) mod 32 =? 0 = true).
  {
    rewrite app_length.
    rewrite H.
    Search ((_ + _) mod _).
    rewrite Nat.add_mod.    
    -{
        Search (_ mod _ = 0).
        rewrite Nat.mod_same.
        -Search (0 + _).
         rewrite plus_O_n.
         unfold cut32 in H0.
         destruct (length l2 mod 32).
         +reflexivity.
         +discriminate.
        -auto.
     }
    -auto.
  }
  rewrite H1.
  assert(length (l1 ++ l2) / 32 = S (length l2 / 32)).
  {
    rewrite app_length.
    rewrite H.
    Check Nat.div_add_l.
    specialize (Nat.div_add_l 1 32 (length l2)).
    intros.
    Search (1 * _).
    rewrite Nat.mul_1_l in H2.
    apply H2.
    auto.    
  }  
  rewrite H2.
  unfold cut32_n.
  assert (firstn 32 (l1 ++ l2) = l1).
  {
    Search (_ = _ -> _ <= _).
    Search firstn.
    Check firstn_app_2.
    rewrite <- H.
    Search (_ + 0).
    specialize (plus_n_O (length l1)).
    intros.
    rewrite H3.
    Check firstn_app_2.
    specialize (firstn_app_2 0 l1 l2).
    intros.
    rewrite H4.
    simpl.
    Search (_ ++ []).
    apply app_nil_r.
  }
  rewrite H3.
  fold cut32_n.
  Search (_ :: _ = _ :: _).
  assert (forall (l1 l2: list (list bool)), l1 = l2 -> Some l1 = Some l2).
  {
    intros.
    rewrite H4.
    reflexivity.
  }
  apply H4.
  Check delete_concat.
  assert (forall (lb : list bool) (ll1 ll2 : list (list bool)), ll1 = ll2 -> lb :: ll1 = lb :: ll2).
  {
    intros.
    rewrite H5.
    reflexivity.
  }
  apply H5.
  unfold cut32 in H0.
  assert (length l2 mod 32 =? 0 = true).
  {
    destruct (length l2 mod 32).
    -reflexivity.
    -simpl in H0.
     discriminate.
  }
  rewrite H6 in H0.
  assert (skipn 32 (l1 ++ l2) = l2).
  {
    SearchAbout skipn.
    assert (firstn 32 (l1 ++ l2) ++ skipn 32 (l1 ++ l2) = (l1 ++ l2)).
    {
      apply firstn_skipn.
    }
    rewrite H3 in H7.
    Search (_ ++ _ = _ ++ _).
    apply app_inv_head in H7.
    auto.
  }
  rewrite H7.
  inversion H0.
  assert (forall (n : nat), n / 32 = fst (Nat.divmod n 31 0 31)).
  {
    destruct n.
    -reflexivity.
    -reflexivity.
  }
  rewrite H8.
  reflexivity.
Qed.
  
Lemma concat_listes_cut32 : forall (ll : list (list bool)) (l : list bool) ,
    concat_listes_32 ll = Some l -> cut32 l = Some ll.
Proof.
  assert (I : forall (ll : list (list bool)) (l : list bool), concat_listes_32 ll = Some l -> cut32 l = Some ll).
  {
    induction ll.
    -assert (I_1 : forall l : list bool, concat_listes_32 [] = Some l -> cut32 l = Some []).
     {
       intros.
       simpl in H.
       inversion H.
       reflexivity.
     }
     auto.
    -assert(forall l : list bool, concat_listes_32 (a :: ll) = Some l -> cut32 l = Some (a :: ll)).
     {
       intros.
       unfold concat_listes_32 in H.
       apply bind_rewrite in H.
       destruct H.
       destruct H.
       fold concat_listes_32 in H0.
       destruct (length a =? 32) eqn:H1.
       -{
           inversion H.
           specialize (IHll x).
           apply commut_equal in H0.
           apply IHll in H0.
           Check app_cut32.
           apply app_cut32.           
           -apply beq_nat_true in H1.
            auto.
           -auto.
         }
       -discriminate.
     }
     auto.
  }
  auto.
Qed.           

(* i made separatly the two case proof *)
Lemma cut32_concat_nil : forall (l : list bool),
    cut32 l = Some [] -> concat_listes_32 [] = Some l.
Proof.
  intros.
  assert (cut32 l = Some [] -> length l = 0).
  {
    destruct (length l) eqn:H1.
    -reflexivity.
    -intros.
     unfold cut32 in H0.
     destruct (length l mod 32 =? 0) eqn:H2.
     +destruct (length l / 32) eqn:H3.
      {
        Search (_ / _ = 0).
        specialize (Nat.div_small_iff (length l) 32).
        intros.
        assert (32 <> 0) by auto.
        apply H4 in H5.
        apply beq_nat_true in H2.
        apply H5 in H3.
        assert (forall (n' m': nat), n' = S m' -> n' < 32 -> n' mod 32 = n').
        {
          intros.
          apply Nat.mod_small.
          auto.
        }
        apply Nat.mod_small in H3.
        rewrite H3 in H2.
        rewrite H1 in H2.
        discriminate.        
      }
      {
        unfold cut32_n in H0.
        fold cut32_n in H0.
        inversion H0.
      }
     +discriminate.
  }
  apply H0 in H.
  Search (length _ = 0).
  apply length_zero_iff_nil in H.
  rewrite H.
  reflexivity.
Qed.


Lemma cut32_length : forall (l l': list bool) (ll : list (list bool)),
    cut32 l = Some (l' :: ll) -> length l' = 32.
Proof.
  assert (div_S_n : forall (n m q : nat), n / m = S q -> m <= n).
  {
    intros.
    apply Nat.div_str_pos_iff.
    -destruct m.
     +discriminate.
     +auto.
    -rewrite H.
     apply Nat.lt_0_succ.
  }
  intros.
  unfold cut32 in H.
  destruct (length l mod 32 =? 0) eqn:H1.
  -destruct (length l / 32) eqn:H2.
   +simpl in H.
    discriminate.
   +unfold cut32_n in H.
    fold cut32_n in H.
    assert (32 <= length l) by (specialize (div_S_n (length l) 32 n);auto).
    assert (forall (l1 l2: list bool) (tl1 tl2 : list (list bool)), Some (l1 :: tl1) = Some (l2 :: tl2) -> l1 = l2).
    { intros. inversion H3. reflexivity. }
    apply H3 in H.
    rewrite <- H.
    Search firstn.
    apply firstn_length_le.
    auto.
  -discriminate.
Qed.


Lemma cut32_firstn : forall (l l': list bool) (ll : list (list bool)),
    cut32 l = Some (l' :: ll) -> firstn 32 l = l'.
Proof.
  intros.
  unfold cut32 in H.
  destruct (length l mod 32 =? 0) eqn:H0.
  -unfold cut32_n in H.
   destruct ((length l / 32)) eqn:H1.
   +discriminate.
   +fold cut32_n in H.
    inversion H.
    reflexivity.
  -discriminate.
Qed.

Lemma skipn_length : forall (l : list bool), 32 <= length l -> length (skipn 32 l) = length l - 32.
Proof.
  Search skipn.
  intros.
  specialize (firstn_skipn 32 l).
  intros.
  rewrite <- H0.
  rewrite app_length.
  Search firstn.
  rewrite firstn_length_le.
  -rewrite minus_plus.
   rewrite H0.
   reflexivity.
  -auto.
Qed.  
Search (_ mod _ = 0).

(* Lemma mod_zero : forall (n m : nat), n mod m = 0 -> n = 0 \/ exists (a : nat),  a * n = m. *)
(* Proof. *)
(*   intros. *)
(*   Search (_ mod _ = 0). *)
(*   apply Nat.div_exact in H. *)
(*   -right. *)
(*    rewrite H. *)
(*    Search (_ * (_ / _)). *)
(*    admit. *)
(*   - *)
   

Lemma mod_sub : forall (n : nat), n mod 32 = 0 -> (n - 32) mod 32 = 0.
Proof. 
  intros.
  specialize (Nat.mod_divides n 32).
  intros.
  assert (32 <> 0) by auto.
  apply H0 in H1.
  apply H1 in H.
  destruct H.
  rewrite H.
  Search (_ * _ - _).
  rewrite <- Nat.mul_pred_r.
  induction x.
  -reflexivity.
  -Search (Nat.pred (S _)).
   rewrite <- pred_Sn.
   Search (_ * _ mod _ = 0).
   Search (_ * _ = _ * _).
   rewrite Nat.mul_comm.
   apply Nat.mod_mul.
   auto.
Qed.

Lemma equal_succ_diff_0 : forall (n' m' : nat), n' = S m' -> 0 < n'.
Proof.
  intros.
  rewrite H.
  Search (0 < S _).
  apply Nat.lt_0_succ.
Qed.

(* XXX: clean up *)
Lemma div_sub : forall (n m k : nat), m <> 0 -> n / m = S k -> (n - m) / m = k.
Proof.
intros.
assert (n = m * (S k) + n mod m).
rewrite <- H0.
apply Nat.div_mod; auto.
rewrite H1.
rewrite Nat.mul_succ_r.
replace (m * k + m + n mod m - m) with (m * k + n mod m).
rewrite Nat.mul_comm.
rewrite Nat.div_add_l; auto.
rewrite Nat.div_small.
now rewrite plus_n_O.
apply Nat.mod_upper_bound; auto.

replace (m * k + m + n mod m - m) with (m * k + (m + n mod m - m)).
now rewrite -> Nat.add_cancel_l, minus_plus.
rewrite Nat.add_sub_assoc, plus_assoc. reflexivity.
apply le_plus_l.
Qed.

Lemma diff_zero : forall (n : nat), 32 <= n -> n <> 0.
Proof.
  destruct n.
  -Search (_ <= 0).
   intros.
   apply Nat.nle_succ_0 in H.
   inversion H.
  -auto.
Qed.

Lemma cut32_concat_listes : forall (ll : list (list bool)) (l : list bool),
    cut32 l = Some ll -> concat_listes_32 ll = Some l.
Proof.
  induction ll.
  -apply cut32_concat_nil.
  -intros.
   assert (cut32 (skipn 32 l) = Some ll).
   {
     unfold cut32 in H.
     destruct (length l mod 32 =? 0) eqn:H0.
     -destruct (length l / 32) eqn:H1.
      +simpl in H.
       discriminate.
      +unfold cut32_n in H.
       fold cut32_n in H.
       assert (forall (a b : list bool) (l1 l2 : list (list bool)), Some (a :: l1) = Some (b :: l2) -> Some l1 = Some l2).
       {
         intros.
         inversion H2.
         reflexivity.
       }
       apply H2 in H.
       assert (forall (ll1 ll2 : list (list bool)), Some ll1 = Some ll2 -> ll1 = ll2).
       {
         intros. inversion H3. reflexivity.
       }
       apply H3 in H.
       unfold cut32.
       assert (32 <= length l).
       {
         Search (_ / _).
         Check Nat.div_str_pos_iff.
         specialize (Nat.div_str_pos_iff (length l) 32).
         intros.
         assert (32 <> 0) by auto.
         apply H4 in H5.
         apply equal_succ_diff_0 in H1.
         apply H5 in H1.
         auto.                      
       }
       assert (length (skipn 32 l) mod 32 =? 0 = true).
       {
         assert (length (skipn 32 l) = length l - 32).
         {
           Check skipn_length.
           apply skipn_length.
           auto.
         }
         rewrite H5.
         auto.
         Check mod_sub.
         specialize (mod_sub (length l)).
         intros.
         apply beq_nat_true in H0.
         apply mod_sub in H0.
         rewrite H0.
         reflexivity.
       }
       rewrite H5.
       assert ((length (skipn 32 l) / 32) = n).
       {
         Check skipn_length.
         rewrite skipn_length.
         -apply div_sub in H1.
          auto.
          assert (length l <> 0).
          {
            apply diff_zero in H4.
            auto.
          }
          auto.
         -auto.         
       }
       rewrite H6.
       rewrite H.
       reflexivity.
     -discriminate.
   }
   simpl.
   specialize (IHll (skipn 32 l)).
   rewrite IHll.
   +assert (length a =? 32 = true).
    {
      Check cut32_length.
      apply cut32_length in H.
      rewrite H.
      reflexivity.
    }
    rewrite H1.
    assert (l = firstn 32 l ++ skipn 32 l).
    {
      rewrite firstn_skipn.
      reflexivity.
    }
    assert (a = firstn 32 l).
    {
      apply cut32_firstn in H.
      apply commut_equal.
      auto.
    }
    rewrite H3.
    unfold bind.
    rewrite <- H2.
    reflexivity.
   +auto.
Qed.




(* Finals goal of this file, proofs about encode_flux_b and decode_flux_b *)
(*=encode_decode_flux_decoup *)
Lemma encode_decode_flux_decoup : forall (lb : list bool) (l : list instruction),
    encode_flux_b l = Some lb -> decode_flux lb = Some l.
(*=End *)
Proof.
  intros.
  unfold encode_flux_b in H.
  destruct encode_flux eqn:H1.
  -Search (encode_flux).
   apply encode_decode_decoup_flux_decoup in H1.
   unfold decode_flux.
   Search concat_listes_32.
   apply concat_listes_cut32 in H.
   rewrite H.
   auto.   
  -discriminate.
Qed.

(*=decode_flux_decoup_encode *)
Lemma decode_flux_decoup_encode : forall (lb : list bool) (l : list instruction), 
    decode_flux lb = Some l -> encode_flux_b l = Some lb.
(*=End *)
Proof.
  intros.
  unfold decode_flux in H.
  unfold encode_flux_b.
  destruct (cut32 lb) eqn:H1.
  -simpl in H. Search (decode_flux_decoup).
   apply decode_decoup_encode_flux in H.
   rewrite H.
   Search cut32.
   apply cut32_concat_listes in H1.
   rewrite H1.
   reflexivity.
  -simpl in H.
   discriminate.
Qed.  




