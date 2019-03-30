(** * Thin (pre)categories *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.

Local Open Scope cat.

(** Thin (posetal) (pre)categories are those with at most one arrow in each hom-set *)

Definition is_thin (C : precategory) : hProp := homtype_hlevel 1 C.

Lemma thin_category_has_homsets (C : precategory) :
  is_thin C -> has_homsets C.
Proof.
  intros H ? ?.
  apply hlevelntosn.
  unfold is_thin, homtype_hlevel in *.
  exact (H _ _).
Qed.

(** Unfortunately, it's difficult to *)