(* https://coq.inria.fr/tutorial-nahas *)

Lemma A_implies_A : (forall A : Prop, A -> A).
Proof.
intros A.
intros proof_of_A.
exact proof_of_A.
Qed.

Lemma not_A_implies_not_A : (forall A : Prop, (~A) -> (~A)).
Proof.
intros A.
unfold not.
intros proof_that_A_implies_False.
exact proof_that_A_implies_False.
Qed.

Theorem not_not_forward : (forall A : Prop, A -> ~(~A)).
Proof.
unfold not. 
intros A.
intros proof_of_A.
intros A_implies_False.
pose (proof_of_False:= A_implies_False proof_of_A).
exact proof_of_False.
Qed.

Theorem not_not_backward : (forall A : Prop, A -> ~(~A)).
Proof.
unfold not.
intros A.
intros proof_of_A A_implies_False.
refine (A_implies_False _).
exact proof_of_A.
Qed.

Theorem and_commutes : (forall A B, A /\ B -> B /\ A).
Proof.
intros A B.
intros A_and_B.

case A_and_B.
intros proof_of_A proof_of_B.

refine (conj _ _).
exact proof_of_B.
exact proof_of_A.
Qed.

Theorem and_commutes_destruct : (forall A B, A /\ B -> B /\ A).
Proof.
intros A B.
intros A_and_B.

destruct A_and_B as [ proof_of_A proof_of_B].

refine (conj _ _).
exact proof_of_B.
exact proof_of_A.
Qed.