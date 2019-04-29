(** * Transporting limits over equivalences of categories *)

Require Import UniMath.Foundations.Preamble.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Local Open Scope cat.

Section Limits.
  Context {C D : category} {F : functor C D} {g : graph}.
  Context (E : adj_equivalence_of_precats F) (lims : Lims_of_shape g D).
  Search adj_equivalence_of_precats.

  Let E' := adj_equivalence_of_precats_inv E.
  Let ESE' := functor_from_equivalence_is_essentially_surjective _ _ _ E'.
  Let G := right_adjoint E.

  (** This specific instance of "right adjoints preserve limits" *)
  Local Lemma rapl
        (d : diagram g D) (L : ob D) (ccL : cone d L) :
    preserves_limit G d L ccL.
  Proof.
    apply right_adjoint_preserves_limit.
    - apply is_right_adjoint_right_adjoint.
    - apply homset_property.
    - apply homset_property.
  Defined.

  (* Local Definition ε : nat_iso (F ∙ G) (functor_identity C). *)
  (* Proof. *)
  (*   use make_nat_iso. *)
  (*   apply (unit_from_left_adjoint E). *)

  Local Definition ε_inv : nat_iso (F ∙ G) (functor_identity C).
  Proof.
    apply (counit_nat_iso_from_adj_equivalence_of_precats
          (adj_equivalence_of_precats_inv E)).
  Defined.

  Local Definition nat_iso_to_pointwise_iso {A B : precategory} {F G : functor A B}
    (n : nat_iso F G) (x : ob A) : iso (F x) (G x) := make_iso _ (pr2 n x).

  Local Lemma diagram_iso {d : diagram g C} :
    ∏ v : vertex g, iso (dob (mapdiagram G (mapdiagram F d)) v) (dob d v).
  Proof.
    intros v; apply (nat_iso_to_pointwise_iso ε_inv).
  Defined.

  Lemma transport_limit_over_equivalence : Lims_of_shape g C.
  Proof.
    intros d.
    pose (d' := mapdiagram F d).
    pose (L' := lims d').
    pose (isLimCone_G_L' := rapl d' _ _ (pr2 L')).
    use make_LimCone.
    - exact (G (pr1 (pr1 L'))).
    - use make_cone.
      + intros v.
        refine (coneOut (mapcone G d' (pr2 (pr1 L'))) v · _).
        apply diagram_iso.
      + intros u v e.
        cbn.

End Limits.