(* Why3 goal *)
Theorem Q_TreeWalk_Exists_Value_Recursive : forall (k:addr),
  forall (mptr_0:(map.Map.map addr addr)), forall (mint_0:(map.Map.map addr
  Z)), forall (v:Z), (is_sint32 v) -> ((p_valid_TreeWalk_ptr k) ->
  ((p_TreeWalk_Exists_Value mptr_0 mint_0 k v) <-> ((~ (k = (Mk_addr 0%Z
  0%Z))) /\ ((v = (map.Map.get mint_0 (shift k 4%Z))) \/
  ((p_TreeWalk_Exists_Value mptr_0 mint_0 (map.Map.get mptr_0 (shift k 0%Z))
  v) \/ (p_TreeWalk_Exists_Value mptr_0 mint_0 (map.Map.get mptr_0 (shift k
  1%Z)) v)))))).
Proof.
intros k mptr_0 mint_0 v h1 h2.
split.
+ intros. 
  destruct (fix_p_TreeWalk_Exists_Value k mptr_0 mint_0 v).
  split. 
  - apply H0.
    apply H.
  - apply H0.
    apply H.
+ intros.
  apply fix_p_TreeWalk_Exists_Value. 
  split.
  - apply H.
  - split.
    * apply h2.
    * apply H.
Qed.
