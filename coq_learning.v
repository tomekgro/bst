(* https://coq.inria.fr/tutorial-nahas *)
(* https://coq.inria.fr/refman/tactic-index.html *)

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

Theorem triple_not_1 : (forall A : Prop, ~A -> ~(~(~A))).
Proof.
intros A.
unfold not.
intros not_A.
intros double_not_A_implies_False.
refine (double_not_A_implies_False _).
exact not_A.
Qed.

Theorem triple_not_2 : (forall A : Prop, ~~~A -> ~A).
Proof.
unfold not.
intros A.
intros triple_not_A.
intros proof_of_A.
refine (triple_not_A _).
intros not_A.
refine (not_A _).
exact proof_of_A.
Qed.

Require Import Bool.
(*
Definition eqb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Definition Is_true (b:bool) :=
  match b with
    | true => True
    | false => False
  end.
*)

(* "simpl" deciphers a definition *)

Theorem thm_eqb_a_t: (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
intros a.
case a.
(* a true *)
simpl.
intros proof_of_True.
exact I.
(* a false *)
simpl.
intros proof_of_False.
case proof_of_False.
Qed.

Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
intros A B.
intros proof_of_A.
refine (or_introl _).
exact proof_of_A.
Qed.

Theorem or_commutes : (forall A B, A \/ B -> B \/ A).
Proof.
intros A B.
intros proof_of_A_or_B.
case proof_of_A_or_B.
(* A is true *)
intros proof_of_A.
refine (or_intror _).
exact proof_of_A.
(* B is true *)
intros proof_of_B.
refine (or_introl _).
exact proof_of_B.
Qed.

Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
intros a b.
unfold iff.
refine (conj _ _).

intros H.

case a,b.
simpl.
refine (conj _ _).
exact I.
exact I.

simpl in H.

case H.
simpl in H.
case H.
simpl in H.
case H.

intros H.

case a,b.
simpl.
exact I.

simpl in H.
destruct H as [T F].
case F.

simpl in H.
destruct H as [F T].
case F.

simpl in H.
destruct H as [F1 F2].
case F1.

Qed.

Theorem negb_is_not : (forall a, Is_true (negb a) <-> (~(Is_true a))).
Proof.
intros a.
unfold iff.
refine (conj _ _).

(* negb -> not *)
case a.
(* a true *)
intros H.
simpl in H.
case H.
(* a false *)
intros H.
simpl in H.
unfold not.
intros H1.
simpl in H1.
case H1.

(* not -> negb *)
unfold not.
case a.
(* a true *)
simpl.
intros not_True.
refine (not_True _).
exact I.
(* a false *)
simpl.
intros not_False.
exact I.

Qed.

(* The proposition "ex P" should be read:
"P is a function returning a Prop and there exists an argument
to that function such that (P arg) has been proven".
The function "P" is known as "the predicate". The constructor for "ex P"
takes the predicate "P" , the witness (called "x" here)
and a proof of "P x" in order to return something of type "ex P". *)

Theorem thm_forall_exists : (forall b, (exists a, Is_true(eqb a b))).
Proof.
intros b.
case b.
(* b true *)
pose (witness:= true).
refine (ex_intro _ witness _).
simpl.
exact I.
(* b false *)
pose (witness:= false).
refine (ex_intro _ witness _).
simpl.
exact I.
Qed.

Theorem thm_eq_trans : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
intros x y z.
intros x_equals_y.
destruct x_equals_y as [].
intros x_equals_z.
destruct x_equals_z as [].
exact eq_refl.
Qed.

Theorem thm_eq_trans_with_rewrite : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
intros x y z.
intros x_y y_z.
rewrite x_y.
rewrite y_z.
exact (eq_refl z).
Qed.

Theorem andb_sym : (forall a b, a && b = b && a).
Proof.
intros a b.
case a,b.
(* true true *)
simpl.
exact eq_refl.
(* false true *)
simpl.
exact eq_refl.
(* true false *)
simpl.
exact eq_refl.
(* false false *)
simpl.
exact eq_refl.
Qed.

Theorem plus_sym: (forall n m, n + m = m + n).
Proof.
intros n m.
elim m.
(* base case for m *)

elim n.
(* base case for n *)
simpl.
exact eq_refl.
(* inductive case for n *)
intros n0.
intros inductive_hypothesis.
simpl.
rewrite inductive_hypothesis.
simpl.
exact eq_refl.

(* inductive case for m *)
intros n0.
intros inductive_hypothesis.
simpl.
rewrite <- inductive_hypothesis.

elim n.
(* base case for n *)
simpl.
exact eq_refl.
(* inductive case for n *)
intros n1.
intros inductive_hypothesis1.
simpl.
rewrite <- inductive_hypothesis1.
exact eq_refl.
Qed.

