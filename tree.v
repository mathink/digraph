(* Tree on Ssreflect *)
Require Import 
Ssreflect.ssreflect
Ssreflect.ssrfun
Ssreflect.ssrbool
Ssreflect.eqtype
Ssreflect.ssrnat
Ssreflect.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope tree_scope with tree.
Open Scope tree_scope.


(** * Definition of [tree] and [forest] *)
Inductive tree (T: Type) :=
| node (x: T)(c: forest T)
with
forest (T: Type) :=
| leaf 
| sibl (t: tree T)(f: forest T).
Arguments leaf {T}.

(** ** Notations *)
Infix "-:" := node (at level 60, no associativity): tree_scope.
Notation "[*]" := leaf: tree_scope.
Infix "~+" := sibl (at level 60, right associativity): tree_scope.
Notation "[~ X + .. + Y ~]" := (X ~+ ( .. (Y ~+ [*]) ..)) (at level 60, right associativity): tree_scope.

(** ** Induction principles  *)
Scheme tree_forest_ind := Induction for tree Sort Prop
  with forest_tree_ind := Induction for forest Sort Prop.
Scheme tree_forest_rec := Induction for tree Sort Set
  with forest_tree_rec := Induction for forest Sort Set.
Scheme tree_forest_rect := Induction for tree Sort Type
  with forest_tree_rect := Induction for forest Sort Type.

(** *** Mutual Induction Principle *)
Combined Scheme tree_forest_mut_ind from
         tree_forest_ind, forest_tree_ind.

(** * Traverse [tree] and [forest] by pre- and post- order *)
Section Traverse.

  Variables (T: Type).
  Implicit Type t : tree T.
  Implicit Type f : forest T.

  Fixpoint size_tree t: nat :=
    match t with
      | x -: f => (size_forest f).+1
    end with
  size_forest f: nat :=
    match f with
      | [*] => 0
      | t ~+ f => size_tree t + size_forest f
    end.
  
  Lemma size_tree_ltn0 t:
    0 < size_tree t.
  Proof.
    by move: t => [x f] //.
  Qed.  

  Lemma size_forest0leaf f:
    size_forest f = 0 -> f = [*].
  Proof.
    move: f => [| t f] //= Heq.
    by move: Heq (ltn_addr (size_forest f) (size_tree_ltn0 t)) => <-; rewrite ltnn.
  Qed.
  

  Fixpoint cat_forest f1 f2 :=
    match f1 with
      | [*] => f2
      | t ~+ f => t ~+ (cat_forest f f2)
    end.
  Infix "+++" := cat_forest (at level 50, left associativity).

  Lemma cat_forest_leaf f:
    f +++ [*] = f.
  Proof.
    by elim: f => [| t f /= ->] //.
  Qed.

  Lemma cat_forest_app f1 f2 f3:
    (f1 +++ f2) +++ f3 = f1 +++ (f2 +++ f3).
  Proof.
    by elim: f1 => [| t f /= ->] //.
  Qed.


  Fixpoint rev_tree t :=
    match t with
      | x -: f => x -: rev_forest f
    end with
  rev_forest f :=
    match f with
      | [*] => [*]
      | t ~+ f => rev_forest f +++ (rev_tree t ~+[*])
    end.

  Lemma cat_rev_forest f1 f2:
    rev_forest (f1 +++ f2) = rev_forest f2 +++ rev_forest f1.
  Proof.
    by elim: f1 => [/= | t f /= ->] //;
      rewrite ?cat_forest_leaf ?cat_forest_app.
  Qed.

  Lemma rev_rev_id:
    (forall t, rev_tree (rev_tree t) = t)
    /\(forall f, rev_forest (rev_forest f) = f).
  Proof.
    apply: tree_forest_mut_ind.
    by move => a c //= ->.
    done.
    by move => t Heqt f Heqf //=; rewrite cat_rev_forest /= Heqt Heqf.
  Qed.


  Fixpoint preorder_tree t :=
    let: x -: f := t in [:: x & preorder_forest f ]
  with preorder_forest f :=
    if f is t ~+ f
    then preorder_tree t ++ preorder_forest f
    else [::].

  Lemma preorder_f_forest_cat f1 f2:
      preorder_forest (f1 +++ f2) = preorder_forest f1 ++ preorder_forest f2.
  Proof.
    by elim: f1 => [| t f /= ->] //; rewrite catA.
  Qed.


  Fixpoint postorder_tree t :=
    let: x -: f := t in rcons (postorder_forest f) x
  with postorder_forest f :=
    if f is t ~+ f
    then postorder_tree t ++ postorder_forest f
    else [::].


  Lemma pre_rev_eq_rev_post:
    (forall t, preorder_tree (rev_tree t) = rev (postorder_tree t))/\
    (forall f, preorder_forest (rev_forest f) = rev (postorder_forest f)).
  Proof.
    apply: tree_forest_mut_ind => [x c /= -> || /= t Heqt f Heqf] //;
      first by rewrite rev_rcons.
    by rewrite rev_cat -Heqt -Heqf preorder_f_forest_cat //= catA cats0. 
  Qed.

  Lemma pre_rev_eq_rev_post_tree t:
    preorder_tree (rev_tree t) = rev (postorder_tree t).
  Proof.
    apply pre_rev_eq_rev_post.
  Qed.

  Lemma pre_rev_eq_rev_post_forest f:
    preorder_forest (rev_forest f) = rev (postorder_forest f).
  Proof.
    apply pre_rev_eq_rev_post.
  Qed.

End Traverse.

Infix "+++" := cat_forest (at level 50, left associativity).

Lemma tree_forest_mut_rect:
  forall (T: Type)(P : tree T -> Type) (Q : forest T -> Type),
    (forall (x : T) (c : forest T), Q c -> P (node x c)) ->
    Q leaf ->
    (forall t, P t -> forall f, Q f -> Q (sibl t f)) ->
    (forall t, P t) * (forall f, Q f).
Proof.
  move => T P Q IHn IHl IHs.
  exact (tree_forest_rect IHn IHl IHs, forest_tree_rect IHn IHl IHs).
Qed.

Section EqTree.

  Variable T: eqType.
  Implicit Type t : tree T.
  Implicit Type f : forest T.

  Fixpoint eqtree t1 t2 :=
    match t1, t2 with
      | x1-:c1, x2-:c2 => (x1 == x2) && (eqforest c1 c2)
    end with
  eqforest f1 f2 :=
    match f1, f2 with
      | [*], [*] => true
      | t1 ~+ f1, t2 ~+ f2 => (eqtree t1 t2) && (eqforest f1 f2)
      | _, _ => false
    end.


  Lemma eqtreeP_eqforestP:
    (Equality.axiom eqtree)*(Equality.axiom eqforest).
  Proof.
    apply: tree_forest_mut_rect
    => [x f IHf [x' f'] | [| t f] | t IHt f IHf [|t' f']] /=; try by constructor.
    - case: (x =P x') => [<- | Hneq]; last by right; case.
        by case: (IHf f') => [<- | Hneq] /=; [ left | right; case ].
    - move: (IHt t') => [<- | Hneq]; last by right; case.
        by move: (IHf f') => [<- | Hneq]; [left | right; case].
  Qed.

  Definition eqtreeP: Equality.axiom eqtree := fst eqtreeP_eqforestP.
  Definition eqforestP: Equality.axiom eqforest := snd eqtreeP_eqforestP.

  Canonical tree_eqMixin := EqMixin eqtreeP.
  Canonical tree_eqType :=  Eval hnf in EqType (tree T) (EqMixin eqtreeP).

  Lemma eqtreeE : eqtree = eq_op.
  Proof.
      by [].
  Qed.
  
  Canonical forest_eqMixin := EqMixin eqforestP.
  Canonical forest_eqType := Eval hnf in EqType (forest T) forest_eqMixin.
  
  Lemma eqforestE : eqforest = eq_op.
  Proof.
      by [].
  Qed.

  Lemma eqtree_node x1 x2 f1 f2:
    (x1 -: f1 == x2 -: f2) = (x1 == x2) && (f1 == f2).
  Proof.
      by [].
  Qed.

  Lemma eqforest_sibl t1 t2 f1 f2:
    (t1 ~+ f1 == t2 ~+ f2) = (t1 == t2) && (f1 == f2).
  Proof.
      by [].
  Qed.


  Fixpoint mem_tree (t: tree T): pred T :=
    match t with
      | node y f => xpredU1 y (mem_forest f)
    end
  with mem_forest (f: forest T): pred T :=
    match f with
      | leaf => xpred0
      | sibl t f => xpredU (mem_tree t) (mem_forest f)
    end.

  Definition eqtree_class := tree T.
  Identity Coercion tree_of_eqtree : eqtree_class >-> tree.

  Coercion pred_of_eq_tree (t : eqtree_class) : pred_class := [eta mem_tree t].
  Canonical tree_predType := @mkPredType T (tree T) pred_of_eq_tree.
  Canonical mem_tree_predType := mkPredType mem_tree.


  Definition eqforest_class := forest T.
  Identity Coercion forest_of_eqforest : eqforest_class >-> forest.

  Coercion pred_of_eq_forest (f : eqforest_class) : pred_class := [eta mem_forest f].
  Canonical forest_predType := @mkPredType T (forest T) pred_of_eq_forest.
  Canonical mem_forest_predType := mkPredType mem_forest.

  Lemma in_node y f x:
    (x \in node y f) = (x == y) || (x \in f).
  Proof.
    by [].
  Qed.

  Lemma in_leaf x:
    (x \in leaf) = false.
  Proof.
    by [].
  Qed.

  Lemma in_sibl x t f:
    (x \in sibl t f) = (x \in t) || (x \in f).
  Proof.
    by [].
  Qed.

  Lemma mem_tree1 x y:
    (x \in node y leaf) = (x == y).
  Proof.
    by rewrite in_node orbF //.
  Qed.

  Let inE := (mem_tree1, in_node, inE).

  Lemma mem_f_cat x f1 f2 :
    (x \in f1 +++ f2) = (x \in f1) || (x \in f2).
  Proof.
    elim: f1 => [//=| t f /= Heq].
    by rewrite in_sibl in_sibl Heq orbA //=.
  Qed.

End EqTree.
Definition inE := (mem_tree1, in_node, inE).

Section TravIn.

  Variables (T: eqType).
  Implicit Type t : tree T.
  Implicit Type f : forest T.

  Lemma traverse_correct_pre:
    (forall t x, (x \in t) == (x \in preorder_tree t))/\
    (forall f x, (x \in f) == (x \in preorder_forest f)).
  Proof.
    apply tree_forest_mut_ind.
    - move=> x f Heq y.
      by rewrite in_node in_cons; move: (Heq y) => /eqP ->.
    - move=> x //=.
    - move=> t Heqt f Heqf x /=.
      by rewrite in_sibl mem_cat; move: (Heqt x) (Heqf x) => /eqP -> /eqP ->.
  Qed.

  Theorem traverse_correct_pre_tree t x:
    (x \in t) == (x \in preorder_tree t).
  Proof.
    move: t x; apply traverse_correct_pre.
  Qed.
  

  Lemma traverse_correct_post:
    (forall t x, (x \in t) == (x \in postorder_tree t))/\
    (forall f x, (x \in f) == (x \in postorder_forest f)).
  Proof.
    apply tree_forest_mut_ind.
    - move=> x f Heq y.
      by rewrite in_node mem_rcons; move: (Heq y) => /eqP ->.
    - move=> x //=.
    - move=> t Heqt f Heqf x.
      by rewrite in_sibl mem_cat; move: (Heqt x) (Heqf x) => /eqP -> /eqP ->.
  Qed.

  Theorem traverse_correct_post_tree t x:
    (x \in t) == (x \in postorder_tree t).
  Proof.
    move: t x; apply traverse_correct_post.
  Qed.

End TravIn.