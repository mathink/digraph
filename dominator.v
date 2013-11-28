(* Directed finite graph  *)

Require Import
  Ssreflect.ssreflect Ssreflect.ssrbool
  Ssreflect.ssrfun Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq
  Ssreflect.path Ssreflect.fintype
  Ssreflect.fingraph.

Set Implicit Arguments.
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)


(* Lemma *)
Lemma connect_uniqP {T: finType}(e: rel T) x y:
  reflect (exists p, path e x p /\ y = last x p /\ uniq (x::p)) (connect e x y).
Proof.
  apply /iffP.
  apply connectP.
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


Module Digraph.
  
  Structure mixin_of (T: finType) :=
    Mixin { dig: T -> seq T }.

  Section ClassDef.
    Structure class_of (T: Type):=
      Class { base: Finite.class_of T;
              mixin: mixin_of (@Finite.Pack T base T) }.
    Local Coercion base: class_of >-> Finite.class_of.
    
    Structure type := 
      Pack { sort;
             _: class_of sort;
             _: Type }.
    Local Coercion sort: type >-> Sortclass.

    Variables (T : Type) (cT : type).
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T' _ _ := cT in T'.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0: mixin_of (@Finite.Pack T b0 T)) :=
      fun bT b & phant_id (Finite.class bT) b =>
        fun m & phant_id m0 m => Pack (@Class T b m) T.

    Definition finType := @Finite.Pack cT xclass xT.
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Finite.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion finType : type >-> Finite.type.
    Canonical finType.
    Notation digType := type.
    Notation DigType T m := (@pack T _ m _ _ id _ id).
    Notation DigMixin := Mixin.
    Notation "[ 'digType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
                                                   (at level 0, format "[ 'digType'  'of'  T  'for'  cT ]") : form_scope.
    Notation "[ 'digType' 'of' T ]" := (@clone T _ _ id)
                                          (at level 0, format "[ 'digType'  'of'  T ]") : form_scope.
  End Exports.

End Digraph.
Import Digraph.Exports.

Definition digraph T := Digraph.dig (Digraph.class T).
Definition digrel (T: digType) := grel (digraph T).

Module CFG.
  
  Section Properties.
    Variables (T: digType)(root: T).
    
    Definition reachable := forall (v: T), connect (digrel T) root v.

  End Properties.

  Structure mixin_of (T: digType) :=
    Mixin { root: T;
            _: reachable T root }.
  
  Local Notation digType_for T b := (@Digraph.Pack T b T).
  Section ClassDef.

    Structure class_of (T: Type) :=
      Class { base: Digraph.class_of T;
              mixin: mixin_of (digType_for T base) }.
    Local Coercion base: class_of >-> Digraph.class_of.
    
    Structure type := 
      Pack { sort;
             _: class_of sort;
             _: Type }.
    Local Coercion sort: type >-> Sortclass.
 
    Variables (T : Type) (cT : type).
    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T' _ _ := cT in T'.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0: mixin_of (digType_for T b0)) :=
      fun bT b & phant_id (Digraph.class bT) b => 
        fun m & phant_id m0 m => Pack (@Class T b m) T.

    Definition finType := @Finite.Pack cT xclass xT.
    Definition digType := @Digraph.Pack cT xclass xT.
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Digraph.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion finType : type >-> Finite.type.
    Canonical finType.
    Coercion digType : type >-> Digraph.type.
    Canonical digType.
    Notation cfgType := type.
    Notation CfgType T m := (@pack T _ m _ _ id _ id).
    Notation CfgMixin := Mixin.
    Notation "[ 'cfgType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
                                                   (at level 0, format "[ 'cfgType'  'of'  T  'for'  cT ]") : form_scope.
    Notation "[ 'cfgType' 'of' T ]" := (@clone T _ _ id)
                                          (at level 0, format "[ 'cfgType'  'of'  T ]") : form_scope.
  End Exports.

End CFG.
Import CFG.Exports.

Definition dig_pred_sort (T : digType) (pT : predType T) := pred_sort pT.
Identity Coercion pred_sort_of_dig : dig_pred_sort >-> pred_sort.

Definition cfg_pred_sort (T : cfgType) (pT : predType T) := pred_sort pT.
Identity Coercion pred_sort_of_cfg : cfg_pred_sort >-> pred_sort.

Definition root (T: cfgType) := CFG.root (CFG.class T).

Section Dominator.

  Variables (V: cfgType).
  (* ERROR: 通らない。 pred_sort 某 が必要と言われる *)
  Definition dominate (u v: V) :=
    forall (p: seq V),
      path (digrel V) (root V) p -> v = last (root V) p -> u \in ((root V)::p).


  Variables (V: finType)(E: rel V)(r: V).

  Hypothesis reachable:
    forall (v: V), connect E r v.

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


End CFG.

