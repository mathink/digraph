(* Directed finite graph  *)

Require Import
  Ssreflect.ssreflect Ssreflect.ssrbool
  Ssreflect.ssrfun Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  Ssreflect.fintype
  MathComp.path MathComp.fingraph.

Require Import tree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Lemma *)
Lemma connect_uniqP {T: finType}(e: rel T) x y:
  reflect (exists p, path e x p /\ y = last x p /\ uniq (x::p)) (connect e x y).
Proof.
  apply /iffP; [| apply connectP | |].
  - move => [p Hp Heq].
    apply shortenP in Hp.
    rewrite -Heq in Hp.
    destruct Hp.
    exists p'.
    repeat split; done.
  - move => [p [Hp [Heq Huniq]]].
    exists p; done.
Qed.

Lemma in_uniq_cat {T: eqType}(s1 s2: seq T):
  uniq (s1 ++ s2) -> forall x, x \in s1 -> x \notin s2.
Proof.
  rewrite cat_uniq.
  move => /and3P [Huniq1 Hnhas Huniq2] x.
    by move: Hnhas => /hasPn //= H; apply contraL, H.
Qed.
  
Lemma uniq_last_nil {T: eqType}(x: T) p:
  uniq (x::p) -> x = last x p -> p = [::].
Proof.
  move: p => [| h t] //= /and3P [Hninx Hninh Huniq] Heq.
  move: Hninx; rewrite Heq mem_last //=.
Qed.

Lemma last_cat_notin {T: eqType}(x y: T) s1 s2:
  x = last y (s1 ++ s2) -> x \notin s2 -> s2 = [::].
Proof.
  move: x y s1.
  pattern s2.
  apply last_ind; first done.
  move => s x IH y z s1.
  rewrite last_cat last_rcons mem_rcons in_cons negb_or;
    move => -> /andP [Hneq _] //=; move: Hneq => /eqP //=.
Qed.    


Section CFG.

  Variables (V: finType)(E: rel V)(r: V).

  Hypothesis reachable: forall (v: V), connect E r v.

  Definition dominate (u v: V) :=
    forall (p: seq V),
      path E r p -> v = last r p -> u \in (r::p).

  Lemma dominate_root u:
    dominate r u.
  Proof.
    rewrite /dominate; move => p Hp Heq.
    by rewrite in_cons; apply /orP; left.
  Qed.

  Lemma dominate_refl u:
    dominate u u.
  Proof.
    by rewrite /dominate; move => p Hp ->; apply mem_last.
  Qed.

  Lemma dominate_antisym u v:
    dominate u v -> dominate v u -> u == v.
  Proof.
    rewrite /dominate.
    move => Huv Hvu.
    move: (reachable u) => /connect_uniqP [p1 [Hp1 [Heq1 Huniq1]]].
    move: (Hvu p1 Hp1 Heq1); rewrite in_cons; move => /orP.
    move => [Heqvr | Hin1].
    - move: Heqvr (eq_refl r) => /eqP Heqvr /eqP H.
      rewrite Heqvr in Huv; rewrite Heqvr.
      by move: (Huv [::] is_true_true H) => //=; rewrite mem_seq1.
    - move: (splitPr Hin1) => Hsplit1; destruct Hsplit1.
      rewrite -cat1s catA cat_path cats1 in Hp1.
      move: Hp1 => /andP [Hp1 _].
      move:  (Huv (rcons p1 v) Hp1 (esym (last_rcons r p1 v))) => Hin.
      rewrite -(cat1s v) catA cats1 -cat_cons in Heq1 Huniq1 Hin1 *.
      move: (last_cat_notin Heq1 (in_uniq_cat Huniq1 Hin)) => Heq.
      by move: Heq1; rewrite Heq cats0 last_rcons; move=> -> //=.
  Qed.      

  Lemma dominate_trans u v w:
    dominate u v -> dominate v w -> dominate u w.
  Proof.
    rewrite {2 3}/dominate.
    move => Huv Hvw p Hp Heq.
    move: (Hvw p Hp Heq); rewrite in_cons; move => /orP [Heqv | Hinv].
    - move: Heqv => /eqP Heqv; subst v.
      move: (dominate_antisym (@dominate_root u) Huv) => /eqP <- //=.
      by rewrite in_cons; apply /orP; left.
    - move: (splitPr Hinv) => Hsplit.
      destruct Hsplit as [pl pr].
      rewrite /dominate in Huv.
      rewrite -cat1s catA cat_path cats1 in Hp.
      move: Hp => /andP [Hp _].
      move: (Huv (rcons pl v) Hp (esym (last_rcons r pl v))) => Hin.
      by rewrite -(cat1s v) catA -cat_cons cats1 mem_cat; apply /orP; left.
  Qed.


  Lemma dominate_lemma:
    forall (u1 u2 v: V),
      dominate u1 v -> dominate u2 v ->
      dominate u1 u2\/dominate u2 u1.
  Proof.
    rewrite /dominate.
    move => u1 u2 v Hdom1 Hdom2;
      move: (reachable v) => /connect_uniqP [p [Hp [Heq Huniq]]].

    move: (Hdom1 p Hp Heq); rewrite in_cons;
      move=> /orP [/eqP -> | Hin1];
        first by left=> p' _ _; rewrite in_cons; apply /orP; left.
    move: (Hdom2 p Hp Heq); rewrite in_cons;
      move=> /orP [/eqP-> | Hin2];
        first by right=> p' _ _; rewrite in_cons; apply /orP; left.

    apply splitPr in Hin1; destruct Hin1 as [pl pr].
    move: Huniq Hp Heq Hin2.
    rewrite cons_uniq cat_path (mem_cat u2) in_cons;
      move=> /= /andP [Hnin Huniq] /and3P [Hpl He1 Hpr] Heqlast.
    move: (in_uniq_cat Huniq) => Hinin /or3P [Hin2l | /eqP -> | Hin2r];
      [| by left=> p _ ->; apply mem_last |].

    - right=> p Hp Heq.
      move: (conj Hp Hpr) => /andP; rewrite Heq -cat_path; move => Hpath.
      rewrite last_cat last_cons Heq -last_cat in Heqlast.
      move: (Hdom2 (p++pr) Hpath Heqlast); rewrite in_cons mem_cat.
      by move: (Hinin u2 Hin2l); rewrite in_cons negb_or andbC -eqbF_neg;
        move => /andP [/eqP -> _]; rewrite orbC -orbA orbC in_cons.

    - left=> p Hp Heq.
      rewrite cat_uniq cons_uniq in Huniq;
        move: Huniq => /and3P [_ _ /andP [Hnin1 _]].
      apply splitPr in Hin2r; destruct Hin2r as [pm pr].
      rewrite cat_path /= in Hpr; move: Hpr => /and3P [Hpm He2 Hpr].
      move: (conj Hp Hpr) => /andP; rewrite Heq -cat_path; move=> Hpath.
      rewrite last_cat last_cons last_cat last_cons Heq -last_cat in Heqlast.
      move: (Hdom1 (p++pr) Hpath Heqlast); rewrite in_cons mem_cat.
      rewrite mem_cat orbC negb_or in_cons orbC negb_or -eqbF_neg in Hnin1.
      by move: Hnin1 => /andP [/andP [/eqP -> _] _];
        rewrite orbC -orbA orbC in_cons /=.
  Qed.

  
  Definition strict_dominate (u v: V): Prop :=
    dominate u v /\ u <> v.

  Definition dominate_frontier (u: V)(vl: seq V): Prop :=
    forall v: V, v \in vl ->
                       ~strict_dominate u v/\
                       exists p: V,
                         E p v /\ dominate u p.

  Definition idom (u v: V): Prop :=
    dominate u v /\ u <> v /\ forall w, dominate w v -> dominate w u.

  Lemma idom_uniq u v w:
    idom u v -> idom w v -> u = w.
  Proof.
    rewrite /idom.
    move=> [Hdomuv [Hnequv Hu]] [Hdomwv [Hneqwv Hw]].
    apply Hu in Hdomwv; apply Hw in Hdomuv.
    by move: (dominate_antisym Hdomuv Hdomwv) => /eqP.
  Qed.

(* Natural Loop *)

  Structure backEdge :=
    BackEdge { head: V;
               tail: V;
               dom: dominate head tail;
               back: E tail head }.

  Definition naturaloop (be: backEdge)(x: V) :=
    dominate (head be) x /\
    (exists p,
       [/\ path E x p , last x p = tail be & head be \notin p]).

  Definition naturaloop_include (be1 be2: backEdge) :=
    forall x: V, naturaloop be1 x -> naturaloop be2 x.

  Lemma dominate_pred (u v: V):
    dominate u v -> u != v ->
    forall x, E x v -> dominate u x.
  Proof.
    rewrite/dominate.
    move=> Hdom Hneq x He.
    move=> p' Hpath Hlast.
    have H0: path E r (rcons p' v);
      first by rewrite rcons_path; apply/andP;
      split; last rewrite -Hlast.
    have H1: v = last r (rcons p' v);
      first by rewrite last_rcons.
    move: (Hdom (rcons p' v) H0 H1).
    rewrite in_cons mem_rcons in_cons.
    move=> /or3P [/eqP Heq | /eqP Heq | Hin].
    - by rewrite Heq in_cons; apply/orP; left.
    - rewrite Heq eq_refl in Hneq; done.
    - by rewrite in_cons; apply/orP; right.
  Qed.

  Lemma dominate_path (u v w: V)(p: seq V):
    dominate u v -> dominate u w ->
    path E v p -> u \notin p -> last v p = w ->
    forall x, x \in p -> dominate u x.
  Proof.
    move: p w => p; pattern p; apply last_ind; first done.
    clear p; move=> p h IH w Hdomuv Hdomuw.
    rewrite rcons_path; move=> /andP [Hpath Hrel] Hnin Hlast x.
    rewrite last_rcons in Hlast; subst.
    rewrite mem_rcons in_cons; move=> /orP [/eqP -> //=| Hin].
    rewrite mem_rcons in_cons negb_or in Hnin.
    move: Hnin => /andP [Heq Hnin].
    apply (IH (last v p)); try done.
    clear Hin.
    move: Hrel.
    apply dominate_pred; try done.
  Qed.    


  Lemma naturaloop_nest (be1 be2: backEdge):
    head be1 != head be2 ->
    naturaloop be1 (head be2) ->
    naturaloop_include be2 be1.
  Proof.
    rewrite/naturaloop /=.
    move: be1 be2 => [h1 t1 Hdom1 Hrel1] [h2 t2 Hdom2 Hrel2] /= Hneq.
    move=> [Hdom12 [p12 [Hpath12 [Hlast12 Hnin12]]]] x.
    move=> [Hdom [p [Hpath [Hlast Hnin]]]].
    split; first by apply dominate_trans with h2.
    exists (p ++ h2::p12).
    split.
    - rewrite cat_path //=; apply/and3P;
      split; by [| rewrite Hlast |].
    - by rewrite last_cat.
    - rewrite mem_cat negb_or in_cons negb_or.
      apply/and3P; split; try done.
      move: {+}Hnin.
      apply contraNN.
      move => Hin1.
      move:
        (dominate_path Hdom Hdom2 Hpath Hnin Hlast Hin1) => Hdom21.
      move: (dominate_antisym Hdom12 Hdom21) => /eqP Heq.
      rewrite Heq eq_refl in Hneq; done.
  Qed.

End CFG.


Definition State (S X: Type) := S -> (X*S).
Definition emb {S X: Type}(x: X): State S X :=
  fun s: S => (x,s).
Definition bind {S X Y: Type}
           (f: X -> State S Y)(m: State S X): State S Y :=
  fun s: S => let (x,s') := m s in f x s'.

Definition get {S: Type}: State S S := fun s => (s,s).
Definition put {S: Type}(s: S): State S S := fun s' => (s',s).
Definition run {S X: Type}(s: S)(m: State S X): X := (m s).1.

Notation "m >>= f" := (bind f m) (at level 65, left associativity).
Notation "m >> p" := (bind (fun _ => p) m) (at level 65, left associativity).
Notation "x <- m ; p" := (m >>= fun x => p) (at level 60, right associativity).
Notation "(: x , y :) <- m ; p" := (m >>= fun tup:_*_ => let: (x,y) := tup in p) (at level 60, right associativity).
Notation "'do' m" := m (at level 100, right associativity).

Definition modify {S: Type}(f: S -> S): State S S :=
  do s <- get;
     put (f s).

Lemma bind_emb S X :
  forall (m: State S X)(s: S),
    run s (m >>= emb) = run s m.
Proof.
  intros m s; unfold run, emb, bind; destruct (m s); reflexivity.
Qed.

Lemma emb_bind S X Y:
  forall (f: X -> State S Y)(x: X)(s: S),
    run s (f x >>= emb) = run s (f x).
Proof.
  intros f x s; unfold run, emb, bind;
  destruct (f x s); reflexivity.
Qed.

Lemma bind_assoc S X Y Z:
  forall (f: X -> State S Y)(g: Y -> State S Z)(m: State S X)(s: S),
    run s (m >>= f >>= g)
    = run s (m >>= (fun x => f x >>= g)).
Proof.
  intros f g m s; unfold run, emb, bind.
  destruct (m s); reflexivity.
Qed.  


Section DFS.

  Fixpoint foldlM {S X Y: eqType}
           (op: Y -> X -> State S Y)(e: Y)(l: seq X): State S Y :=
    if l is [:: h & t]
    then do e' <- op e h;
            foldlM op e' t
    else emb e.
  
  Variable T: eqType.           (* for test *)
  (* Variable T: finType. *)
  Variable g: T -> seq T.

  Fixpoint dfs_forestM (n: nat)(h: forest T)(x: T)
  : State (seq T) (forest T) :=
    do v <- get;
       if (x \in v) then emb h
       else if n is n'.+1
       then do _ <- put (x::v);
               h' <- foldlM (dfs_forestM n') leaf (g x);
               emb (sibl (node x h') h)
       else emb h.

  Definition dfs_treeM (n: nat)(x: T)
  : State (seq T) (tree T) :=
    do _ <- modify (cons x);
       h' <- foldlM (dfs_forestM n) leaf (g x);
       emb (node x h').

End DFS.

Definition g (n: nat) :=
  match n with
    | 0 => [:: 1 ]
    | 1 => [:: 2; 8]
    | 2 => [:: 3; 4]
    | 3 => [:: 5; 6]
    | 4 => [:: 6]
    | 5 => [:: 7]
    | 6 => [:: 7]
    | 7 => [:: 14]
    | 8 => [:: 9; 10; 11]
    | 9 => [:: 13]
    | 10 => [:: 13; 15]
    | 11 => [:: 12]
    | 12 => [:: 8]
    | 13 => [:: 14]
    | 14 => [:: 16]
    | 15 => [:: 14]
    | _ => [::]
  end.

Eval compute in (run [::] (dfs_treeM g 20 0)).

Fixpoint foldl_tree {X Y: Type}(op: Y -> X -> Y)(e: Y)(t: tree X): Y :=
  let (n,f) := t in foldl_forest op (op e n) f
with foldl_forest {X Y: Type}(op: Y -> X -> Y)(e: Y)(f: forest X): Y :=
       match f with
         | leaf => e
         | sibl t f' => foldl_forest op (foldl_tree op e t) f'
       end.

Eval compute in
    (foldl_forest plus 0 (run [::] (dfs_forestM g 10 leaf 0))).
Eval compute in
    (foldl_tree plus 0 (run [::] (dfs_treeM g 10 0))).
