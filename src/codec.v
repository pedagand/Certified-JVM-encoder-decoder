Require Import ast_instructions.
Require Import association_list.
Require Import binary.

(* Product decoding function in order to get 2 types. eg: (Opcode * arguments) *)
Fixpoint crossDecode (A B: Type) (l: list bool) (dA: list bool -> (A*list bool)) (dB: list bool -> (B*list bool)) : (A*B*list bool) :=
  match dA l with
  | (a, l') => match dB l' with
               | (b, l'') => (a,b,l'')
               end
  end.

(* Returns the decoded result from a decoding function *)
Fixpoint getResultDecode (A: Type) (l: list bool) (decode: list bool -> (A*list bool)) : A :=
  match decode l with
  | (a, l') => a
  end.

(* Returns the remainding list from a decoding function *)
Fixpoint getRemListDecode (A: Type) (l: list bool) (decode: list bool -> (A*list bool)) : list bool :=
  match decode l with
  | (a, l') => l'
  end.

(* We want to prove the correctness of the decoding function *) 
(* Lemma decode_composition : forall (A B: Type) (l: list bool) (dA: list bool -> (A*list bool)) (dB: list bool -> (B*list bool)),
    . *)