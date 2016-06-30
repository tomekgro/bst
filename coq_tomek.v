Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).


Lemma nat_trichotomy : forall a b : nat, a=b \/ a<b \/ a>b.

Lemma le_n : forall n : nat, n = n \/ n<n.

Lemma le_S : forall n : nat, n <= S n.
 
Lemma S_greater: forall a:nat, (S a)>a.
Proof.
intros a.
apply le_n.
Qed.
 
Lemma nat_greater: forall a : nat, exists b:nat, b=(S a) /\ a<b.
Proof.
intros a.
refine (ex_intro _ (S a) _).
refine (conj _ _).



 
Lemma nat_between : forall a b : nat, (b-a=2)->(a<b)/\(exists c:nat, a<c /\ c<b).

Proof.
 intros a b.
 split.

Lemma nat_two_between: forall a b : nat, (b-a=3) -> exists c:nat, 
a<c /\ a<b /\ c<b /\ (exists d:nat, a<d /\ c<d /\ d<b).

Proof.
 intros a b.
 intros c.

Fixpoint sum_n n :=
match n with
0 => 0
| S p => p + sum_n p
end.

(*
https://coq.inria.fr/tutorial-nahas
intros A = assume A 
exact - means that proof of out temporary goal is on the list above
*)

Theorem my_first_proof : (forall A : Prop, A -> A).
Proof.
  intros A.
  intros proof_of_A.
  exact proof_of_A.
Qed.

Theorem forward_small : (forall A B : Prop, A -> (A->B) -> B).
Proof.
 intros A.
 intros B.
 intros proof_of_A.
 intros A_implies_B.
 pose (proof_of_B := A_implies_B proof_of_A).
 exact proof_of_B.
Qed.

Theorem backward_small : (forall A B : Prop, A -> (A->B)->B).
Proof.
 intros A B.
 intros proof_of_A A_implies_B.
 refine (A_implies_B _).
   exact proof_of_A.
Qed.

Theorem backward_large : (forall A B C : Prop, A -> (A->B) -> (B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B B_implies_C.
 refine (B_implies_C _).
   refine (A_implies_B _).
     exact proof_of_A.
Qed.

Theorem backward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 refine (A_imp_B_imp_C _ _).
   exact proof_of_A.

   refine (A_implies_B _).
     exact proof_of_A.
Qed.

Theorem not_not_1 : (forall A : Prop, A -> ~(~A)).
Proof.
unfold not. 
intros A.
intros proof_of_A.
intros A_implies_False.
pose (proof_of_False:= A_implies_False proof_of_A).
exact proof_of_False.
Qed.

Theorem False_cannot_be_proven__again : ~False.
Proof.
  unfold not.
  intros proof_of_False.
  case proof_of_False.
Qed.

Theorem exists_forall : (forall P : Set->Prop, ~(exists x, P x) -> (forall x, ~(P x))).
Proof.
  intros P.
  intros not_exists_x_Px.
  intros x.
  unfold not.
  intros P_x.
  unfold not in not_exists_x_Px.
  refine (not_exists_x_Px _).
    exact (ex_intro P x P_x).
Qed.

Theorem absurd2 : forall A C : Prop, A -> ~ A -> C.
Proof.
  intros A C.
  intros proof_of_A proof_that_A_cannot_be_proven.
  unfold not in proof_that_A_cannot_be_proven.
  pose (proof_of_False := proof_that_A_cannot_be_proven proof_of_A).
  case proof_of_False.
Qed.

Theorem thm_true_imp_false : ~(True -> False).
Proof.
  intros T_implies_F.
  refine (T_implies_F _).
    exact I.
Qed.



Require Import Bool.

Theorem true_is_True: Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem not_eqb_true_false: ~(Is_true (eqb true false)).
Proof.
  simpl.
  unfold not.
  intros proof_of_False.
  exact proof_of_False. (* Not recommended, I know. Just wanted to try.. *)
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
(* suppose a is true *)
    simpl.
    exact I.

(* suppose a is false *)
    simpl.
    exact I.
Qed.

 Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
(* orb -> \/ *)
    intros H.
    case a, b.
(* suppose a,b is true, true *)
      simpl.
      refine (or_introl _).
        exact I.

(* suppose a,b is true, false *)
      simpl.
      exact (or_introl I).

(* suppose a,b is false, true *)
      exact (or_intror I).

(* suppose a,b is false, false *)
      simpl in H.
      case H.

(* \/ -> orb *)
    intros H.
    case a, b.
(* suppose a,b is true, true *)
      simpl.
      exact I.

(* suppose a,b is true, false *)
      exact I.

(* suppose a,b is false, true *)
      exact I.

(* suppose a,b is false, false *)
      case H.
(* suppose H is (or_introl A) *)
         intros A.
         simpl in A.
         case A.

(* suppose H is (or_intror B) *)
         intros B.
         simpl in B.
         case B.
Qed.

Definition basic_predicate
:=
  (fun a => Is_true (andb a true))
.

Theorem thm_exists_basics : (ex basic_predicate).
Proof.
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
    simpl.
    exact I.
Qed.

Theorem thm_forall_exists__again : (forall b, (exists a, Is_true(eqb a b))).
Proof.
  intros b.
  refine (ex_intro _ b _).
(* witness is b *)
  exact (eqb_a_a b).
Qed.

Theorem exists_foralll : (forall P : Set->Prop, ~(exists x, P x) -> (forall x, ~(P x))).
Proof.
intros P.
intros not_exists_x_Px.
intros x.
unfold not.
intros P_x.
unfold not in not_exists_x_Px.
refine (not_exists_x_Px _).
exact (ex_intro P x P_x).
Qed.

Theorem forall_exists : (forall P : Set->Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
intros P.
intros forall_x_not_Px.
unfold not.
intros exists_x_Px.
destruct exists_x_Px as [ witness proof_of_Pwitness].
pose (not_Pwitness := forall_x_not_Px witness).
unfold not in not_Pwitness.
pose (proof_of_False := not_Pwitness proof_of_Pwitness).
case proof_of_False.
Qed.

Theorem thm_eq_sym : (forall x y : Set, x = y -> y = x).
Proof.
  intros x y.
  intros x_y.
  destruct x_y as [].
  exact (eq_refl x).
Qed.

Theorem neq_nega: (forall a, a <> (negb a)).
Proof.
intros a.
unfold not.
case a.
(* true *)
intros true_false.
discriminate true_false.
(* false *)
intros false_true.
discriminate false_true.
Qed.

Theorem plus_2_3 : (S (S O)) + (S (S (S O))) = (S (S (S (S (S O))))).
Proof.
  simpl.
  exact eq_refl.
Qed.

Theorem plus_n_0 : (forall n, n + O = n).
Proof.
intros n.
elim n.
(* base case *)
simpl.
exact eq_refl.
(* inductive case *)
intros n0.
intros inductive_hypothesis.
simpl.
rewrite inductive_hypothesis.
exact eq_refl.
Qed.

Theorem plus_sym: (forall n m, n + m = m + n).
Proof.
intros n m.
elim n.

(* base case for n *)
simpl.
elim m.
simpl.
exact eq_refl.

intros n0.
intros ind_hyp.
simpl.
rewrite <- ind_hyp.
exact eq_refl.

(* inductive case for n *)
intros n0.
intros ind_hyp.
simpl.
rewrite ind_hyp.
elim m.
simpl.
exact eq_refl.

intros n1.
intros ind_hyp_1.
simpl.
rewrite ind_hyp_1.
exact eq_refl.
Qed.

Require Import List.

Theorem cons_adds_one_to_length :
  (forall A:Type,
  (forall (x : A) (lst : list A),
  length (x :: lst) = (S (length lst)))).
Proof.
  intros A.
  intros x.
  intros lst.
  simpl.
  exact eq_refl.
Qed.

Definition hd (A : Type) (default : A) (l : list A)
:=
  match l with
    | nil => default
    | x :: _ => x
  end.

Definition my_hd_for_nat_lists
:=
  hd nat 0.

Compute my_hd_for_nat_lists nil.

Compute my_hd_for_nat_lists (5 :: 4 :: nil).


