(** * Limits in the precategory of types

  This is a partial reconstruction of the results of "Homotopy limits in type
  theory" by Jeremy Avigad, Chris Kapulkin, and Peter LeFanu Lumsdaine
  (arXiv:1304.0680v3).

  Eventually, this should probably be moved into CategoryTheory, but there is
  no proof of the universal property ([isLimCone]) as phrased in
  [CategoryTheory.limits.graphs.limits]. *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.Univalence.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.Types.

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Local Open Scope cat.

(** The constructions after this section are made easier by observing that arrows in
    [type_precat] are actually functions, and we can ask for homotopties between
    them, rather than equalities. *)
Section HomotopyCones.

  Context {g : graph}.

  (** Compare to [cone]. *)
  Definition homot_cone (d : diagram g type_precat) (c : type_precat) : UU :=
    ∑ (f : ∏ (v : vertex g), type_precat⟦c,dob d v⟧),
      ∏ (u v : vertex g) (e : edge u v), f u · dmor d e ~ f v.

  Definition mk_homot_cone {d : diagram g type_precat} {c : type_precat}
             (f : ∏ v, type_precat⟦c, dob d v⟧)
             (Hf : ∏ u v (e : edge u v), f u · dmor d e ~ f v) : homot_cone d c :=
    tpair _ f Hf.

  (** These types are equivalent because they are almost identical, that their
      last components are equivalent is due to [weqtoforallpaths]. *)
  Lemma homot_cone_weq_cone (d : diagram g type_precat) (c : type_precat) :
    homot_cone d c ≃ cone d c.
  Proof.
    unfold homot_cone, cone.
    use weqfibtototal; intro f.
    do 3 (use weqonsecfibers; intro).
    apply invweq, weqtoforallpaths.
  Defined.
End HomotopyCones.

Section StandardLimits.

  Context {g : graph} (d : diagram g type_precat).

  Definition standard_limit : UU :=
    ∑ (x : ∏ (v : vertex g), dob d v),
    ∏ (u v : vertex g) (e : edge u v), dmor d e (x u) = x v.

  (** The condition that [standard_limit] is a cone is basically a rephrasing of
      its definition. *)
  Lemma standard_homot_cone : homot_cone d standard_limit.
    use mk_homot_cone; cbn.
    - exact (λ n l, pr1 l n).
    - intros ? ? ? l; apply (pr2 l).
  Defined.

  Definition standard_cone : cone d standard_limit :=
    homot_cone_weq_cone _ _ standard_homot_cone.
End StandardLimits.

(** The following lemma characterizes paths in the type of standard limits.
    It isn't used in the rest of this file, but might be nice to have. *)
Section StandardLimitHomot.

  Context {g : graph} {d : diagram g type_precat} (x y : standard_limit d).

  (** A homotopy of cones *)
  Definition standard_limit_homot : UU :=
    ∑ h : pr1 x ~ pr1 y,
      ∏ (u v : vertex g) (ed : edge u v),
        (maponpaths (dmor d ed) (h u) @ (pr2 y _ _) ed = pr2 x _ _ ed @ (h v)).

  (** Such homotopies can be made into paths *)
  Lemma standard_cone_homot_to_path (h : standard_limit_homot) : x = y.
  Proof.
    apply (total2_paths_f (funextsec _ _ _ (pr1 h))).

    (** transport_lemma in peterlefanulumsdaine/hott-limits/Limits1.v. *)
    assert (transport_lemma :
              ∏ p : pr1 x = pr1 y,
                transportf _ p (pr2 x) = λ u v (ed : edge u v),
                maponpaths (dmor d ed) (!(toforallpaths _ _ _ p u))
                @ pr2 x _ _ ed
                @ toforallpaths _ _ _ p v).
    {
      intros p; induction p; cbn; unfold idfun.
      do 3 (apply funextsec; intro).
      exact (!(pathscomp0rid _)).
    }
    refine (transport_lemma _ @ _).
    apply funextsec; intro u; apply funextsec; intro v; apply funextsec; intro ed.
    rewrite toforallpaths_funextsec.
    replace (pr2 y u v ed) with (idpath _ @ (pr2 y u v ed)) by reflexivity.
    refine (_ @ maponpaths (λ p, p @ _) (pathsinv0l (maponpaths _ (pr1 h u)))).
    refine (_ @ (path_assoc (! maponpaths _ _) (maponpaths _ _) _)).
    rewrite maponpathsinv0.
    apply maponpaths, pathsinv0.
    exact (pr2 h u v ed).
  Defined.
End StandardLimitHomot.

(** The canonical homotopy cone given by an arrow X → Y where Y has a homotopy cone. *)
Definition into_homot_cone_to_homot_cone {X Y : UU} {g : graph} {d : diagram g _}
            (coneY : homot_cone d (Y : ob type_precat)) (f : X → Y) : homot_cone d X.
  use mk_homot_cone.
  - intro ver.
    exact (pr1 coneY ver ∘ (f : type_precat ⟦ X, Y ⟧)).
  - intros ? ? ? ?; apply (pr2 coneY).
Defined.

Section StandardLimitUP.

  Context {g : graph} {d : diagram g type_precat}.

  (** A rephrasing of the universal property: the canonical map that makes a
      cone out of a map X → L is an equivalence. *)
  Definition is_limit_homot_cone {L} (C : homot_cone d L) :=
    ∏ (X : UU), isweq (@into_homot_cone_to_homot_cone X L g d C).

  Definition limit_homot_cone (L : UU) := ∑ C : homot_cone d L, is_limit_homot_cone C.

  Lemma isaprop_is_homot_limit_cone {L} (C : homot_cone d L) :
    isaprop (is_limit_homot_cone C).
  Proof.
    do 2 (apply impred; intro).
    apply isapropiscontr.
  Qed.

  (** A weak equivalence expressing the above universal property. *)
  Definition limit_homot_up_weq {X L} {C : homot_cone d L} {is : is_limit_homot_cone C} :
    (X → L) ≃ homot_cone d X := weqpair (into_homot_cone_to_homot_cone C) (is X).

  (** The universal property of a limit.

      - Proposition 4.2.8 (limit_universal) in Avigad, Kapulkin, and Lumsdaine
      - Generalizes Lemma 10 in Ahrens, Capriotti, and Spadotti
      - Generalizes univ-iso in HoTT/M-types
  *)
  Lemma limit_homot_universal : is_limit_homot_cone (standard_homot_cone d).
    intro X.
    use isweq_iso.
    - intros xcone x.
      unfold standard_limit.
      use tpair.
      + exact (λ ver, pr1 xcone ver x).
      + intros ? ? ?; apply (pr2 xcone).
    - reflexivity.
    - reflexivity.
  Defined.

  (** The universal property as a weak equivalence *)
  Definition standard_limit_homot_up_weq {X} :
    (X → standard_limit d) ≃ homot_cone d X :=
    @limit_homot_up_weq _ _ _ limit_homot_universal.

  (** The universal property in terms of normal cones *)
  Definition standard_limit_up_weq {X} : (X → standard_limit d) ≃ cone d X :=
    weqcomp standard_limit_homot_up_weq (homot_cone_weq_cone _ _).
End StandardLimitUP.
