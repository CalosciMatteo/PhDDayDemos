Import Logic.

Section Intuitionistic.
Context (A B C :Type).

Lemma Then1 : A -> (B -> A).
Proof.
Admitted.

Lemma Then2 : (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
Proof.
Admitted.

Lemma And1 : (A * B) -> A.
Proof.
Admitted.

Lemma And2 : (A * B) -> A.
Proof.
Admitted.

Lemma And3 : A -> (B -> A*B).
Proof.
Admitted.

Print sum.

Lemma Or1 : A -> (A + B). 
Proof.
  Print sum.
  Check inl.
  Check inr.

Admitted.

Lemma Or2 : A -> (A + B). 
Proof.
Admitted.

Lemma Or3 : (A -> C) -> ((B -> C) -> ((A + B) -> C)). 
Proof.
Admitted.

Lemma False : Logic.False -> A.
Proof.
  Print Logic.False.
  Check False_rect.
  (* exfalso. *)
Admitted.


Lemma LEM : (A + (notT A)).
Proof.
Abort.

Check False.

Lemma dnegElim : notT (notT (A + (notT A))).
Proof.
  unfold notT.
  Print notT.
Admitted.

End Intuitionistic.