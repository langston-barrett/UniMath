(* ******************************************************************************* *)
(** * Yoneda Lemma
    Niccolo Veltri, Niels van der Weide
    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OpMorBicat.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.EquivToAdjequiv.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Yoneda.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Representable.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Section YonedaLemma.
  Context {B : bicat}.
  Variable (B_is_univalent_2_1 : is_univalent_2_1 B)
           (F : psfunctor (op1_bicat B) bicat_of_cats)
           (X : B).

  (** First, we construct a functor from the yoneda to the presheaf *)
  Definition yoneda_to_presheaf_data_ob
    : pstrans (representable B_is_univalent_2_1 X) F → pr1 (F X).
  Proof.
    apply TODO.
  Defined.

  Definition yoneda_to_presheaf_data_mor
             (η₁ η₂ : pstrans (representable B_is_univalent_2_1 X) F)
             (m : modification η₁ η₂)
    : yoneda_to_presheaf_data_ob η₁ --> yoneda_to_presheaf_data_ob η₂.
  Proof.
    apply TODO.
  Defined.

  Definition yoneda_to_presheaf_data
    : functor_data
        (univ_hom
           (psfunctor_bicat_is_univalent_2_1
              (op1_bicat B) bicat_of_cats
              univalent_cat_is_univalent_2_1)
           ((y B_is_univalent_2_1) X) F)
        (F X : univalent_category).
  Proof.
    use make_functor_data.
    - exact yoneda_to_presheaf_data_ob.
    - exact yoneda_to_presheaf_data_mor.
  Defined.

  Definition yoneda_to_presheaf_is_functor
    : is_functor yoneda_to_presheaf_data.
  Proof.
    split.
    - apply TODO.
    - apply TODO.
  Qed.

  Definition yoneda_to_presheaf
    : bicat_of_cats
        ⟦ univ_hom
            (psfunctor_bicat_is_univalent_2_1
               _ _ univalent_cat_is_univalent_2_1)
            (y B_is_univalent_2_1 X) F
          , F X ⟧.
  Proof.
    use make_functor.
    - exact yoneda_to_presheaf_data.
    - exact yoneda_to_presheaf_is_functor.
  Defined.

  (** Next, we construct a functor in the opposite direction *)
  Section PresheafToYonedaOb.
    Variable (x : (F X : univalent_category)).

    Definition presheaf_to_yoneda_ob_pstrans_functor_ob
               (Y : op1_bicat B)
      : B ⟦ Y , X ⟧ → pr1 (F Y).
    Proof.
      apply TODO.
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_functor_mor
               (Y : op1_bicat B)
               (f g : B ⟦ Y , X ⟧)
               (α : f ==> g)
      : (presheaf_to_yoneda_ob_pstrans_functor_ob Y f)
          -->
          presheaf_to_yoneda_ob_pstrans_functor_ob Y g.
    Proof.
      apply TODO.
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_functor_data
               (Y : op1_bicat B)
      : functor_data (@hom B Y X) (pr1 (F Y)).
    Proof.
      use make_functor_data.
      - exact (presheaf_to_yoneda_ob_pstrans_functor_ob Y).
      - exact (presheaf_to_yoneda_ob_pstrans_functor_mor Y).
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_is_functor
               (Y : op1_bicat B)
      : is_functor (presheaf_to_yoneda_ob_pstrans_functor_data Y).
    Proof.
      split.
      - apply TODO.
      - apply TODO.
    Qed.

    Definition presheaf_to_yoneda_ob_pstrans_functor
               (Y : op1_bicat B)
      : bicat_of_cats ⟦ @univ_hom B B_is_univalent_2_1 Y X , F Y ⟧.
    Proof.
      use make_functor.
      - exact (presheaf_to_yoneda_ob_pstrans_functor_data Y).
      - exact (presheaf_to_yoneda_ob_pstrans_is_functor Y).
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_nat_trans_data
               (Y₁ Y₂ : op1_bicat B)
               (f : B ⟦ Y₂ , Y₁ ⟧)
      : nat_trans_data
          (presheaf_to_yoneda_ob_pstrans_functor Y₁ · # F f : functor _ _)
          (#(y B_is_univalent_2_1 X : psfunctor _ _) f
            · presheaf_to_yoneda_ob_pstrans_functor Y₂ : functor _ _).
    Proof.
      apply TODO.
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_is_nat_trans
               (Y₁ Y₂ : op1_bicat B)
               (f : B ⟦ Y₂ , Y₁ ⟧)
      : is_nat_trans _ _ (presheaf_to_yoneda_ob_pstrans_nat_trans_data Y₁ Y₂ f).
    Proof.
      apply TODO.
    Qed.

    Definition presheaf_to_yoneda_ob_pstrans_nat_trans
               (Y₁ Y₂ : op1_bicat B)
               (f : B ⟦ Y₂ , Y₁ ⟧)
      : (presheaf_to_yoneda_ob_pstrans_functor Y₁ · # F f)
          ==>
          #(y B_is_univalent_2_1 X : psfunctor _ _) f
          · presheaf_to_yoneda_ob_pstrans_functor Y₂.
    Proof.
      use make_nat_trans.
      - exact (presheaf_to_yoneda_ob_pstrans_nat_trans_data Y₁ Y₂ f).
      - exact (presheaf_to_yoneda_ob_pstrans_is_nat_trans Y₁ Y₂ f).
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_is_nat_iso
               (Y₁ Y₂ : op1_bicat B)
               (f : B ⟦ Y₂ , Y₁ ⟧)
      : is_nat_iso (presheaf_to_yoneda_ob_pstrans_nat_trans Y₁ Y₂ f).
    Proof.
      apply TODO.
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_data
      : pstrans_data ((y B_is_univalent_2_1) X) F.
    Proof.
      pose x.
      use make_pstrans_data.
      - exact presheaf_to_yoneda_ob_pstrans_functor.
      - intros Y₁ Y₂ f.
        use make_invertible_2cell.
        + exact (presheaf_to_yoneda_ob_pstrans_nat_trans Y₁ Y₂ f).
        + apply is_nat_iso_to_is_invertible_2cell.
          exact (presheaf_to_yoneda_ob_pstrans_is_nat_iso Y₁ Y₂ f).
    Defined.

    Definition presheaf_to_yoneda_ob_pstrans_is_pstrans
      : is_pstrans presheaf_to_yoneda_ob_pstrans_data.
    Proof.
      repeat split.
      - apply TODO.
      - apply TODO.
      - apply TODO.
    Qed.

    Definition presheaf_to_yoneda_ob
      : pstrans (y B_is_univalent_2_1 X) F.
    Proof.
      use make_pstrans.
      - exact presheaf_to_yoneda_ob_pstrans_data.
      - exact presheaf_to_yoneda_ob_pstrans_is_pstrans.
    Defined.
  End PresheafToYonedaOb.

  Section PresheafToYonedaMor.
    Variable (a b : (F X : univalent_category))
             (f : a --> b).

    Definition presheaf_to_yoneda_mor_modification_nat_trans_data
               (Y : op1_bicat B)
      : nat_trans_data
          ((presheaf_to_yoneda_ob a) Y : functor _ _)
          ((presheaf_to_yoneda_ob b) Y : functor _ _).
    Proof.
      pose f.
      apply TODO.
    Defined.

    Definition presheaf_to_yoneda_mor_modification_is_nat_trans
               (Y : op1_bicat B)
      : is_nat_trans
          _ _
          (presheaf_to_yoneda_mor_modification_nat_trans_data Y).
    Proof.
      apply TODO.
    Qed.

    Definition presheaf_to_yoneda_mor_modification_data
      : modification_data (presheaf_to_yoneda_ob a) (presheaf_to_yoneda_ob b).
    Proof.
      intros Y.
      use make_nat_trans.
      - exact (presheaf_to_yoneda_mor_modification_nat_trans_data Y).
      - exact (presheaf_to_yoneda_mor_modification_is_nat_trans Y).
    Defined.

    Definition presheaf_to_yoneda_mor_is_modification
      : is_modification presheaf_to_yoneda_mor_modification_data.
    Proof.
      apply TODO.
    Qed.

    Definition presheaf_to_yoneda_mor_modification
      : modification (presheaf_to_yoneda_ob a) (presheaf_to_yoneda_ob b).
    Proof.
      use make_modification.
      - exact presheaf_to_yoneda_mor_modification_data.
      - exact presheaf_to_yoneda_mor_is_modification.
    Defined.
  End PresheafToYonedaMor.

  Definition presheaf_to_yoneda_data
    : functor_data
        (F X : univalent_category)
        (univ_hom
           (psfunctor_bicat_is_univalent_2_1
              (op1_bicat B) bicat_of_cats
              univalent_cat_is_univalent_2_1) ((y B_is_univalent_2_1) X) F).
  Proof.
    use make_functor_data.
    - exact presheaf_to_yoneda_ob.
    - exact presheaf_to_yoneda_mor_modification.
  Defined.

  Definition presheaf_to_yoneda_is_functor
    : is_functor presheaf_to_yoneda_data.
  Proof.
    split.
    - apply TODO.
    - apply TODO.
  Qed.

  Definition presheaf_to_yoneda
    : bicat_of_cats
        ⟦ F X ,
          univ_hom
            (psfunctor_bicat_is_univalent_2_1
               _ _ univalent_cat_is_univalent_2_1)
            (y B_is_univalent_2_1 X) F ⟧.
  Proof.
    use make_functor.
    - exact presheaf_to_yoneda_data.
    - exact presheaf_to_yoneda_is_functor.
  Defined.
End YonedaLemma.
