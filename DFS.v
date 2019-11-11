Require Import Coq.Logic.ProofIrrelevance.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.lib.Equivalence_ext.
Require Import Relations.
Require Import Classical.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.path_lemmas.

Module DFSproof.

Section DFSplayground.

Context {Vertex Edge: Type}.
Context {EV: EqDec Vertex eq}.
Context {EE: EqDec Edge eq}.
Context {pg: PreGraph Vertex Edge}.
Context {st: Vertex}.

Definition state : Type := (list Vertex) * (list Vertex).
Definition empty_state : state := pair nil nil.

Print relation.

Inductive DFS_step: relation state :=
  | DFS_nil_start: 
      vvalid pg st -> DFS_step empty_state (pair (st :: nil) (st :: nil))
  | DFS_forward: forall v v' l vl,
      ~ In v' vl -> edge pg v v' ->
      DFS_step (pair (v :: l) vl) (pair (v' :: v :: l) (v' :: vl))
  | DFS_backward: forall v l vl,
      (forall v', edge pg v v' -> In v' vl) ->
      DFS_step (pair (v :: l) vl) (pair l vl).

Print clos_refl_trans.

Definition DFS: state -> state -> Prop :=
  clos_refl_trans state DFS_step.

Definition DFSn1: state -> state -> Prop :=
  clos_refl_trans_n1 state DFS_step.

Definition DFS1n: state -> state ->  Prop :=
  clos_refl_trans_1n state DFS_step.

Search clos_refl_trans_1n.

Lemma DFS_eq_DFS1n: forall s1 s2, DFS s1 s2 <-> DFS1n s1 s2.
Proof. split; [apply clos_rt_rt1n | apply clos_rt1n_rt]. Qed.

Lemma DFS_eq_DFSn1: forall s1 s2, DFS s1 s2 <-> DFSn1 s1 s2.
Proof. split; [apply clos_rt_rtn1 | apply clos_rtn1_rt]. Qed.

(**************************** state eq_dec ******************************)
Lemma list_eq_dec: forall (l1 l2: list Vertex),
  {l1 = l2} + {l1 <> l2}.
Proof. decide equality; apply EV. Qed.

Lemma state_eq_dec: forall (s1 s2: state),
  {s1 = s2} + {s1 <> s2}.
Proof. decide equality; apply list_eq_dec. Qed.

(*************************** step change ********************************)
Lemma list_add_not_eq: forall (A: Type) (v: A) (l: list A), 
  v :: l <> l.
Proof.
  induction l; unfold not; intros; inversion H; subst; auto.
Qed.

Lemma step_change: forall s1 s2,
  DFS_step s1 s2 -> s1 <> s2.
Proof.
  intros.
  induction H as [H1 | v v' l m H1 H2 | v v' l m];
    unfold not; intros; inversion H; try apply (list_add_not_eq Vertex v' l); 
    try apply (list_add_not_eq Vertex v v') in H1; auto.
Qed.

(********************** vis list not empty ******************************)
Lemma vis_list_not_empty: forall s,
  s <> empty_state -> DFS empty_state s -> length (snd s) > 0.
Proof.
  intros s Hne H.
  rewrite DFS_eq_DFSn1 in H.
  induction H; [exfalso; auto | ].
  inversion H; simpl in *; [auto | apply Gt.gt_Sn_O | ].
  symmetry in H2. subst; simpl in *.
  apply IHclos_refl_trans_n1.
  unfold not. intros.
  subst. inversion H2.
Qed.

(********************** vis list length increasing **********************)
Lemma vis_list_length_incr: forall s1 s2,
  DFS s1 s2 -> length (snd s2) >= length (snd s1).
Proof.
  intros.
  induction H; [ induction H; simpl | | ]; auto.
  unfold ge in *. 
  apply PeanoNat.Nat.le_trans with (m := length (snd y)); auto.
Qed.

(*************************** vis list adding ****************************)
Lemma vis_list_add_step: forall s1 s2,
  DFS_step s1 s2 ->
    (forall v, In v (snd s1) -> In v (snd s2)).
Proof.
  intros.
  induction H; simpl in *; auto.
Qed.

Lemma vis_list_add: forall s1 s2,
  DFS s1 s2 ->
    (forall v, In v (snd s1) -> In v (snd s2)).
Proof.
  intros.
  induction H; auto.
  induction H; simpl; auto.
Qed.

(*************** start vertex must be in vis list ***********************)
Lemma st_in_vis_list: forall s,
  s <> empty_state -> DFS empty_state s -> In st (snd s).
Proof.
  intros.
  apply DFS_eq_DFSn1 in H0.
  induction H0; [exfalso; auto | ].
  assert (K: {y = empty_state} + {y <> empty_state}); [apply state_eq_dec | ].
  destruct K.
  - subst. inversion H0; simpl in *; auto.
  - apply (vis_list_add y z). constructor. auto. auto.
Qed.

(*************** Vertex in stack must be in vis list ********************)
Lemma in_stack_in_vis_list: forall s,
  DFS empty_state s ->
    (forall v, In v (fst s) -> In v (snd s)).
Proof.
  intros s H.
  rewrite DFS_eq_DFSn1 in H.
  induction H; auto; intros.
  inversion H; simpl in *.
  - symmetry in H3, H4; subst; simpl in *; auto.
  - symmetry in H4, H5; subst; simpl in *.
    destruct H1 as [H1 | H1]; auto.
  - symmetry in H3, H4; subst; simpl in *; auto.
Qed.

(******************* Vertex in vis list all reachable *******************)
Theorem vis_list_all_reachable: forall s,
  DFS empty_state s ->
    (forall v, In v (snd s) -> reachable pg st v).
Proof.
  intros s H.
  rewrite DFS_eq_DFSn1 in H.
  induction H; [ intros; exfalso; auto | ].
  assert (K: forall v, {In v (snd y)} + {~ In v (snd y)});
    [intros; apply ListDec.In_dec, EV | ].
  assert (K': forall v, {In v (snd y)} + {~ In v (snd y)}); auto.
  intros.
  specialize K with (v := v).
  destruct K; auto.
  inversion H; simpl in *.
  - symmetry in H3, H4; subst; simpl in *.
    destruct H1; [subst | exfalso; auto].
    apply reachable_ind_reachable; constructor; auto.
  - symmetry in H4, H5; subst; simpl in *.
    destruct H1 as [H1 | H1]; [subst | exfalso; auto].
    clear n. specialize K' with (v := v0).
    destruct K' as [K' | K'].
    specialize IHclos_refl_trans_n1 with (v := v0).
    apply reachable_ind2_reachable.
    apply reachable_ind2_reachable in IHclos_refl_trans_n1; auto.
    apply ind2.reachable_cons with (y := v0); auto.
    assert (J: DFS empty_state (v0 :: l, vl)); [rewrite DFS_eq_DFSn1; auto | ].
    apply in_stack_in_vis_list with (v := v0) in J; simpl in *; [exfalso | ]; auto.
  - symmetry in H3, H4; subst. simpl in *.
    exfalso; auto.
Qed.

(***************** vertex in vis list once get in stack *****************)
(** it may seems useless in the following proof,
    but it provides me a method to proof the next lemma **)
Lemma in_vis_list_once_in: forall v l vl,
  DFS empty_state (l, vl) -> In v vl ->
    (exists l' vl', DFS empty_state (v :: l', v :: vl') /\ DFS (v :: l', v :: vl') (l, vl)).
Proof.
  intros v l vl H Hin.
  remember (l, vl) eqn: Hs.
  revert l vl Hs Hin.
  apply DFS_eq_DFSn1 in H.
  induction H; intros; [inversion Hs; subst; exfalso; auto | ].
  subst. inversion H; subst.
  - inversion Hin; [ | exfalso; auto]. symmetry in H1. subst. clear Hin.
    exists nil. exists nil. split; [repeat constructor; auto | apply rt_refl].
  - inversion Hin; subst.
    + clear Hin.
      exists (v0 :: l0), (vl0).
      split. apply rt_trans with (y := (v0 :: l0, vl0)).
      apply DFS_eq_DFSn1; auto. constructor; constructor; auto.
      apply rt_refl.
    + specialize IHclos_refl_trans_n1 with (l := v0 :: l0) (vl := vl0).
      assert (exists l' vl' : list Vertex,
                         DFS empty_state (v :: l', v :: vl') /\
                         DFS (v :: l', v :: vl') (v0 :: l0, vl0)); auto.
      destruct H2 as [l' [vl' [?H ?H]]].
      exists l', vl'. split. auto. apply rt_trans with (y := (v0 :: l0, vl0)); auto.
      constructor; constructor; auto.
  - specialize IHclos_refl_trans_n1 with (l0 := v0 :: l) (vl0 := vl).
    assert (exists l' vl' : list Vertex,
                         DFS empty_state (v :: l', v :: vl') /\
                         DFS (v :: l', v :: vl') (v0 :: l, vl)); auto.
    destruct H1 as [l' [vl' [?H ?H]]].
    exists l', vl'. split; auto.
    apply rt_trans with (y := (v0 :: l, vl)); auto.
    constructor; constructor; auto.
Qed.

(***************** vertex in vis list once go backward ******************)
Lemma in_vis_list_once_out: forall v l vl,
  DFS empty_state (l, vl) -> In v vl -> ~ (In v l) ->
    (exists l' vl', DFS empty_state (v :: l', vl') /\ DFS_step (v :: l', vl') (l', vl') /\ DFS (l', vl') (l, vl)).
Proof.
  intros v l vl H Hin1 Hin2.
  remember (l, vl) eqn: Hs.
  revert l vl Hs Hin1 Hin2.
  apply DFS_eq_DFSn1 in H.
  induction H; intros; [inversion Hs; subst; exfalso; auto | ].
  inversion H.
  - subst. inversion H3. subst. exfalso; auto.
  - subst. inversion H4. subst. clear H4.
    inversion Hin1; subst.
    + exfalso. apply Hin2. simpl. left. auto.
    + specialize IHclos_refl_trans_n1 with (l := v0 :: l0) (vl := vl0).
      assert (exists l' vl' : list Vertex,
                         DFS empty_state (v :: l', vl') /\
                         DFS_step (v :: l', vl') (l', vl') /\
                         DFS (l', vl') (v0 :: l0, vl0)). {
        apply IHclos_refl_trans_n1; auto.
        unfold not. intros. simpl in H4, Hin2. apply Hin2. tauto.
      }
      destruct H4 as [l' [vl' [?H [?H ?H]]]].
      exists l', vl'. split; [auto | split; auto].
      apply rt_trans with (y := (v0 :: l0, vl0)); auto.
      constructor. constructor; auto.
  - subst. inversion H3. subst. clear H3.
    assert (K: {v = v0} + {v <> v0}); [apply EV | ].
    destruct K as [K | K].
    + subst. exists l, vl.
      split. apply DFS_eq_DFSn1. auto.
      split. auto. apply rt_refl.
    + specialize IHclos_refl_trans_n1 with (l0 := v0 :: l) (vl0 := vl).
      assert (exists l' vl' : list Vertex,
                         DFS empty_state (v :: l', vl') /\
                         DFS_step (v :: l', vl') (l', vl') /\
                         DFS (l', vl') (v0 :: l, vl)). {
        apply IHclos_refl_trans_n1; auto.
        simpl in *. unfold not. intros.
        unfold not in Hin2, K.
        destruct H2; auto.
      }
      destruct H2 as [l' [vl' [?H [?H ?H]]]].
      exists l', vl'. split; auto.
      split; auto.
      apply rt_trans with (y := (v0 :: l, vl)); auto.
      constructor. constructor. auto.
Qed.

(****************** reachable vis list strong edge **********************)
(** when backward from vertex v1, vertex v2, which is linked to vertex v1
    by edge, must be visited. **)
Lemma reachable_vis_list_strong_edge: forall v1 v2 l vl evl,
  DFS empty_state (l, vl) -> DFS (l, vl) (nil, evl) ->
    ~ (In v1 l) -> In v1 vl -> edge pg v1 v2 -> In v2 evl.
Proof.
  intros.
  assert (exists l' vl', DFS empty_state (v1 :: l', vl') /\ DFS_step (v1 :: l', vl') (l', vl') /\ DFS (l', vl') (l, vl)); [apply in_vis_list_once_out; auto | ].
  destruct H4 as [l' [vl' [?H [?H ?H]]]].
  inversion H5.
  - subst. assert (v' :: vl' <> vl'); [apply list_add_not_eq; auto | ].
    exfalso; auto.
  - subst. specialize H8 with (v' := v2).
    assert (In v2 vl'); auto.
    apply (vis_list_add (l', vl') (nil, evl)).
    apply rt_trans with (y := (l, vl)); auto.
    simpl. auto.
Qed.

(********************* reachable vis list strong ************************)
(** when backward from vertex v1, vertex v2, which is reachable from vertex v1
    by edge, must be visited. **)
Lemma reachable_vis_list_strong: forall v1 v2 l vl evl,
  DFS empty_state (l, vl) -> DFS (l, vl) (nil, evl) ->
    ~ (In v1 l) -> In v1 vl -> reachable pg v1 v2 -> In v2 evl.
Proof.
  intros.
  apply reachable_ind2_reachable in H3.
  induction H3; [apply (vis_list_add (l, vl) (nil, evl)); auto | ].
  unfold edge in *.
  assert (In y evl); [apply IHreachable; auto | ].
  apply (reachable_vis_list_strong_edge y z nil evl evl); auto.
  - apply rt_trans with (y := (l, vl)); auto.
  - apply rt_refl.
Qed.


(******************* the definition of end_state ************************)
Definition end_state (s: state) : Prop := forall s', ~ (DFS_step s s').

(*************** Some usefull lemmas about end_state ********************)
(** if s is an end state, then its stack must be empty **)
Lemma end_state_stack_empty: forall s,
  DFS empty_state s -> end_state s -> (fst s) = nil.
Proof.
  intros s H He.
  unfold end_state in He.
  destruct s as [l vl]; simpl in *.
  destruct l; auto.
  assert ((forall v', edge pg v v' -> In v' vl) \/ ~ (forall v', edge pg v v' -> In v' vl)); [apply classic | ].
  destruct H0.
  - specialize He with (s' := (l, vl)). exfalso.
    apply He. constructor. auto.
  - apply not_all_ex_not in H0.
    destruct H0 as [n ?H].
    apply imply_to_and in H0.
    specialize He with (s' := (n :: v :: l, n :: vl)).
    exfalso. apply He. destruct H0. constructor; auto.
Qed.

(** if s is an end state, then its vis list must be empty (if st is valid) **)
Lemma end_state_vis_list_not_empty: forall s, vvalid pg st ->
  DFS empty_state s -> end_state s -> (snd s) <> nil.
Proof.
  intros.
  unfold end_state in *.
  destruct s as [l vl]; simpl in *.
  assert (l = nil); [apply (end_state_stack_empty (l, vl)); auto | subst].
  destruct vl.
  - specialize H1 with (s' := (st :: nil, st :: nil)). exfalso.
    apply H1. constructor. auto.
  - unfold not in *; intros ?H. inversion H2.
Qed.


(************** Vertex reachable in endstate's vis list *****************)
Theorem reachable_vis_list: forall v s, vvalid pg st -> 
  DFS empty_state s -> 
    end_state s ->
      reachable pg st v -> In v (snd s).
Proof.
  intros.
  destruct s as [l vl]. simpl in *.
  unfold end_state in *.
  assert (l = nil); [apply (end_state_stack_empty (l, vl)); auto | subst].
  assert (vl <> nil); [apply (end_state_vis_list_not_empty (nil, vl)); auto | ].
  apply (reachable_vis_list_strong st v nil vl vl); auto.
  - apply rt_refl.
  - apply (st_in_vis_list (nil, vl)); auto.
    unfold not in *. intros. inversion H4. auto.
Qed.

(** the end of the proof of DFS's correctness *)
(************************************************************************)

End DFSplayground.

End DFSproof.