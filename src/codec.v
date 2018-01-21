Require Import ast_instructions.
Require Import association_list.
Require Import binary.
  
Variable A B : Type.
  
(* Simple encoder for unit *)
Definition unitEncode (l: list bool) : (unit*list bool) :=
  (tt, l).

(* Product decoding function in order to decode 2 kinds of data. eg: (Opcode * arguments) *)
Fixpoint crossDecode (l: list bool) (dA: list bool -> (option A*list bool)) (dB: list bool -> (option B*list bool)) : (option A*option B*list bool) :=
  match dA l with
  | (a, l') => match dB l' with
               | (b, l'') => (a,b,l'')
               end
  end.
  
(* Decoding function using 2 given codecs *)
Fixpoint sumDecode (l: list bool) (dA: list bool -> (option A*list bool)) (dB: list bool -> (option B*list bool)) : ((option A + option B)*list bool) :=
  match dA l with
  | (None, l') => match dB l' with
             | (b, l'') => ((inr b),l'')
             end
  | (a, l') => ((inl a),l')
  end.

(* Returns the decoded result from a decoding function. Is it useful ? *)
Fixpoint getResultDecode (l: list bool) (decode: list bool -> (A*list bool)) : A :=
  match decode l with
  | (a, l') => a
  end.

(* Returns the remainding list from a decoding function. Is it useful ?  *)
Fixpoint getRemListDecode (l: list bool) (decode: list bool -> (A*list bool)) : list bool :=
  match decode l with
  | (a, l') => l'
  end.

(* We want to prove the correctness of the decoding function *) 
Lemma decode_composition : forall (l l' l'': list bool) (a: A) (b: B) (dA: list bool -> (A*list bool)) (dB: list (* bool -> (B*list bool)),
  crossDecode l dA dB = (a, b, l'') -> dA l = (a, l') /\ dB l' = (b, l'').
Proof. *)
  