Variable A B : Type.

Lemma codec_none : forall (T: Type) (d: list bool -> (option T*list bool)),
  d nil = (None, nil).
Proof.
  intros.
  
  
(* Simple encoder for unit *)
Definition unitEncode (l: list bool) : (option unit*list bool) :=
  (Some tt, l).
  
(* unitEncode cannot return None *)
Lemma unitEncode_trivial : forall (l : list bool),
  False -> unitEncode l = (None, l).
Proof.
  intros.
  inversion H.
Qed.

(* Product decoding function in order to decode 2 kinds of data. eg: (Opcode * arguments) *)
Fixpoint crossDecode (l: list bool) (dA: list bool -> (option A*list bool)) (dB: list bool -> (option B*list bool)) : (option A*option B*list bool) :=
  match dA l with
  | (a, l') => match dB l' with
               | (b, l'') => (a,b,l'')
               end
  end.
  
Lemma crossDecode_empty : forall (dA: list bool -> (option A*list bool)) (dB: list bool -> (option B*list bool)),
  crossDecode nil dA dB = (None, None, nil).
Proof.
  intros.
  simpl.
  
(* We want to prove the correctness of the cross decoding function *) 
Lemma decode_composition : forall (l: list bool) (a: option A) (b: option B) (dA: list bool -> (option A*list bool)) (dB: list bool -> (option B*list bool)),
  crossDecode l dA dB = (fst (dA l), fst (dB (snd (dA l))), snd (dB (snd (dA l)))).
Proof.
  Admitted.

(* Decoding function using 2 given codecs *)
Fixpoint sumDecode (l: list bool) (dA: list bool -> (option A*list bool)) (dB: list bool -> (option B*list bool)) : ((option A + option B)*list bool) :=
  match dA l with
  | (None, l') => match dB l' with
             | (b, l'') => ((inr b),l'')
             end
  | (a, l') => ((inl a),l')
  end.
  
(* We want to prove the correctness of the sum decoding function *) 
Lemma sum_decode_composition : forall (l: list bool) (a: option A) (b: option B) (dA: list bool -> (option A*list bool)) (dB: list bool -> (option B*list bool)),
  fst (dA l) = None -> sumDecode l dA dB = (inr (fst (dB l)), snd (dB l)).
Proof.
  Admitted.