Open Scope type.

(*TIPO DELLE COPPIE*)
Section prodRules.

  Print prod.
  Print pair.

  Context (A B : Type).
  Context (a:A) (b:B).

  Check A : Type.
  Check B.
  Check a : A.
  Check b.

(*FORMAZIONE*)
  Print pair.

  Check prod A B.
  Check A * B.

(*INTRODUZIONE*)
  Check (a,b).

(*ELIMINAZIONE*)
  Check prod_rect.

  (*simpler example*)
  Context (G : Type).
  (*in the target it can be dependent on A and B*)

  Check @prod_rect A B (fun _ => G)
    : (A -> B -> G) -> (A * B -> G).
  (*To build a function A * B -> G it suffices
    to give a term of G having at disposal
    a term of A and a term of B *)


  (*example: projections*)

  Definition pi1 : (A * B -> A).
  Proof.
    apply prod_rect.
    intros x y.
    exact x.
  Defined.
  Definition pi2 := @prod_rect A B (fun _ => B) (fun x y => y).

  Check pi1 (a,b).
  (*how do we knows this is just a?*)

(*COMPUTATION*)
  Context (f: A -> B -> G).
  Definition f0 := @prod_rect A B (fun _ => G) f
    : A * B -> G.

  Goal f0 (a,b) = f a b.
  Proof.
    cbn.
    reflexivity.
  Qed.
  
  Eval compute in f0 (a,b).


  Eval compute in pi1 (a, b).
  Eval compute in pi2 (a, b).

(*UNIQUENESS, not present in Coq*)
  Context (p : A * B).

  Check (fst p).
  Check (snd p).

  Check (fst p,snd p).

  Goal p = (pi1 p,pi2 p).
  (* Goal p = (fst p,snd p). *)
  Proof.
    Fail reflexivity.
    induction p. (*This just call prod_rect*)
    (*Then all the computation and we are done*)
    cbn.
    reflexivity.
  Qed.

End  prodRules.

Section natRules.
  Print nat.
  
  Check nat. (*FORMATION*)

  Check 0.  (*INTRODUCTION: 0 and S*)
  Check S.

  (*numerals works as shorthand*)
  Eval cbn in S (S (S 0)).

  Check nat_rect. (*ELIMINATION: natural induction*)

  (*COMPUTATION*)
  Context (G : Type).

  Context (g:G).
  Context (f : G -> G).

  Definition gf0 := nat_rect (fun _ => G) g (fun _ => f).

  Eval cbn in gf0 0.
  Eval cbn in gf0 1.
  Eval cbn in gf0 2.
  Eval cbn in gf0 5.

  (*a more concrete example: iseven*)

  Definition iseven : nat -> bool.
  Proof.
    apply nat_rect.
    - exact true.
    - intros n b.
      exact (negb b).
  Defined.

  Eval cbn in iseven 3.

  Eval cbn in iseven 10.
  
End natRules.