
Require Import Frap.





Theorem SocIsMortal : 
  forall men (isMortal :  men -> Prop ),
    (forall m:men , isMortal m)
    -> (forall socrates : men,
      isMortal socrates).
Proof.
  simplify. auto.
Qed.


Theorem SocIsMortal' : 
  forall men (isMortal : men -> Prop ) (socrates:men),
    (forall m : men, isMortal m)
    -> (isMortal socrates).
Proof.
  simplify.
apply H with (m:=socrates).
Qed.



(* https://madiot.fr/coq100/#1 *)

(* sqrt of 2 irrational *)


Definition divisable (a b:nat) : Prop :=  a mod b = 0.

(* perhaps unneeded lemma *)
Lemma even_or_odd : forall n, n mod 2 = 0 \/  n mod 2 = 1.
Proof.
  simplify.

  assert(0 < 2 -> 0 <= n mod 2 < 2). apply Nat.mod_bound_pos. linear_arithmetic.
Admitted.

Theorem sqrt2_not_rational : forall p q, 
  q <> 0 
  -> (forall a, a <> 1 -> ~( (divisable p a) /\ (divisable q a)))
  -> p * p <> q * q * 2.
Proof.
simplify.
  propositional.
  
unfold divisable in *.
assert ((p * p) mod 2 = (q * q * 2) mod 2).
f_equal. apply H1.


assert ((q * q * 2) mod 2 = 0).
apply Nat.mod_mul. auto.

assert ((p * p) mod 2 = 0).
rewrite H3 in H2. auto.

assert ((p mod 2) = 0). admit.


assert (exists k, k * 2 = p). admit.

destruct H6.

rewrite<- H6 in H1.

assert ((x * 2 * x) * 2 = (q * q )* 2). admit.

assert ((x * 2 * x) = (q * q )).  admit.

(* ..... *)
assert (q mod 2 = 0 ).  admit.

apply H0 with (a:=2).

linear_arithmetic.

propositional.

Admitted.





