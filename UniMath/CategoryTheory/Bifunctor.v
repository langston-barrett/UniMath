(** * Bifunctors *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

(** ** Contents

    - Definitions
      - Bifunctors as functors A × B ⟶ C
      - Bifunctors as functors A ⟶ [B, C]
      - Equivalence between the above definitions
 *)

Local Open Scope cat.
Local Notation "A ⊗ B" := (precategory_binproduct A B) (at level 75).

(** ** Definitions *)

Section Definitions.
  Context (A B C : precategory).

  (** A bifunctor is a functor from a product category *)
  Definition bifunctor : UU := (A ⊗ B) ⟶ C.

  (** A bifunctor is a functor into a functor category *)
  Definition bifunctor' (hsC : has_homsets C) : UU := A ⟶ [B, C, hsC].

  Lemma bifunctors_equiv (hsC : has_homsets C) : bifunctor ≃ bifunctor' hsC.
  Proof.
    use weq_iso.
    - intros bif.
      use mk_functor.
      + use mk_functor_data.
        * intros a.
          use mk_functor.
          {  use mk_functor_data.
             - intros b; exact (pr1 bif (precatbinprodpair a b)).
             - intros b c f; cbn.

          }

End Definitions.
