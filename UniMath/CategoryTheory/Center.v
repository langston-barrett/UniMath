(** * Center of a category

The center of a category is the commutative monoid of natural endomorphisms
of the identity functor id : C ⟹ C.

Author: Langston Barrett (@siddharthist)
*)

Require Import UniMath.Foundations.Init.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

Definition nat_trans_hSet {C C' : precategory} (hsC' : has_homsets C')
  (F F' : functor_data C C') : hSet := hSetpair _ (isaset_nat_trans hsC' F F').

Section Center.
  Context {C : precategory}.

  Local Notation "1" := (functor_identity C).

  Definition center : abmonoid.
  Proof.
    (** TODO: use stuff from actions branch *)

End Center.
