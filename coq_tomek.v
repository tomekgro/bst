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

 
Lemma nat_between : forall a b : nat, (b-a=2)->(a<b)/\(exists c:nat, a<c /\ c<b).

Proof.
 intros a b.
 split.

Lemma nat_two_between: forall a b : nat, (b-a=3) -> exists c:nat, 
a<c /\ a<b /\ c<b /\ (exists d:nat, a<d /\ c<d /\ d<b).

Proof.
 intros a b.
 intros c.
