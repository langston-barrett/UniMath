(** * Monoidal categories

Monoidal categories are categories X with a bifunctor ⊗ : X × X ⟶ X
which is associative and unital up to natural isomorphisms.

Note: We do not define monoidal precategories because we need functor categories.

Author: Langston Barrett (@siddharthist)
*)


(** ** Contents :

 - Definition
  - Preliminaries
  - Structure
  - Identities
    - Pentagon identity ([pentagon_identity])
    - Triangle identity ([trangle_identity])
  - Definition ([is_monoidal], [monoidal_category])
 - Symmetric monoidal categories
 - Cartesian monoidal categories

*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

(* Cartesian *)
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Open Scope cat.

Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.Combinatorics.StandardFiniteSets.

(** ** Definition *)

(** *** Preliminaries *)

Local Notation "C ×' D" := (precategory_binproduct C D)
                          (at level 75, right associativity).

(** To state the associativity condition, we'll need a few preliminary
    definitions. Note that we fix the associativity of three-way products
    as (A × B) × C by convention.
 *)

(** Given a functor A × B ⟶ D, construct functors

    - [collapse_left]:  (A × B) × C ⟶ D × C
    - [collapse_right]: A × (B × C) ⟶ A × D
 *)

Local Definition collapse_left {A B C D : precategory} (F : (A ×' B) ⟶ D) :
  ((A ×' B) ×' C) ⟶ (D ×' C) := pair_functor F (functor_identity _).

Local Definition collapse_right {A B C D : precategory} (F : (B ×' C) ⟶ D) :
  (A ×' (B ×' C)) ⟶ (A ×' D) := pair_functor (functor_identity _) F.

(** Given a functor X × X ⟶ X, construct functors (X × X) × X ⟶ X.

    - [left_first] "multiplies" the left factors first
    - [right_first] first appplies the associator (for the
      [precategory_binproduct]) and then "multiplies" the right factors first.
  *)

Local Definition left_first {X : precategory} (F : (X ×' X) ⟶ X) :
  ((X ×' X) ×' X) ⟶ X := (collapse_left F ∙ F).

Local Definition right_first {X : precategory} (F : (X ×' X) ⟶ X) :
  ((X ×' X) ×' X) ⟶ X := (precategory_binproduct_unassoc X X X ∙ collapse_right F ∙ F).

(** A bifunctor is a functor from a product category *)
Local Notation bifunctor A B C := (functor (A ×' B) C).

(** *** Structure *)

(** A monoidal structure on a category X is given by
    1. A [bifunctor] X × X ⟶ X (called the monoidal product and denoted ⊗),
    2. An object I : Ob C (called the unit),
    3. Three natural isomorphisms:
      a. associator (denoted α) : (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)
      b. left unitor (denoted λ) : I ⊗ A ≅ A
      c. right unitor (denoted ρ) : A ⊗ I ≅ A
 *)
Definition monoidal_data
  (** 0 *) (X      : category) : UU :=
  (** 1 *) ∑ (prod : bifunctor X X X)
  (** 2 *)   (I    : ob X),
  (** 2 *)
  (** a *) (@iso [(X ×' X) ×' X, X] (left_first prod) (right_first prod)) ×
  (** b *) (@iso [X, X] (functor_fix_fst_arg _ _ _ prod I) (functor_identity _)) ×
  (** c *) (@iso [X, X] (functor_fix_snd_arg _ _ _ prod I) (functor_identity _)).

(** Constructor *)
Definition mk_monoidal_data (X : category)
  (prod : bifunctor X X X) (I    : ob X)
  (assoc : @iso [(X ×' X) ×' X, X] (left_first prod) (right_first prod))
  (lun : @iso [X, X] (functor_fix_fst_arg _ _ _ prod I) (functor_identity _))
  (run : @iso [X, X] (functor_fix_snd_arg _ _ _ prod I) (functor_identity _))
  : monoidal_data X := tpair _ prod (tpair _ I (dirprodpair assoc (dirprodpair lun run))).

(** Accessor functions *)
Section accessors.
  Context {X : category} (m : monoidal_data X).
  Definition monoidal_prod : bifunctor X X X := (pr1 m).
  Definition monoidal_unit : ob X := (pr1 (pr2 m)).
  Definition associator_iso :
    @iso [(X ×' X) ×' X, X] (left_first monoidal_prod)
                            (right_first monoidal_prod) := pr1 (pr2 (pr2 m)).
  Definition lunit_iso :
    @iso [X, X] (functor_fix_fst_arg _ _ _ monoidal_prod monoidal_unit)
                (functor_identity _) := pr1 (pr2 (pr2 (pr2 m))).
  Definition runit_iso :
    @iso [X, X] (functor_fix_snd_arg _ _ _ monoidal_prod monoidal_unit)
                (functor_identity _) := pr2 (pr2 (pr2 (pr2 m))).
  Definition associator :
    left_first monoidal_prod ⟹
    right_first monoidal_prod := morphism_from_iso _ _ _ associator_iso.
  Definition lunit :
    functor_fix_fst_arg _ _ _ monoidal_prod monoidal_unit ⟹
    functor_identity _ := morphism_from_iso _ _ _ lunit_iso.
  Definition runit :
    functor_fix_snd_arg _ _ _ monoidal_prod monoidal_unit ⟹
    functor_identity _ := morphism_from_iso _ _ _ runit_iso.
End accessors.

(** Notations *)
Notation "A ⊗ B" := (monoidal_prod _ (dirprodpair A B))
                    (right associativity, at level 60) : monoidal_scope.
Notation "1" := (monoidal_unit _) : monoidal_scope.
Notation "0" := (monoidal_unit _) : monoidal_scope.
Notation α A B C := (associator _ (dirprodpair (dirprodpair A B) C)).
Notation λ' A := (lunit _ A).
Notation ρ' A := (runit _ A).

(** *** Identities *)

Local Open Scope monoidal_scope.


Section Identities.
  Context {X : category} (mdata : monoidal_data X).

  (* These might make this more or less clear... *)
  (*
  Notation "x ⊗# f" := (# (functor_fix_fst_arg _ _ _ (monoidal_prod _) x) f)
                      (right associativity, at level 60) : monoidal_scope.
  Notation "f #⊗ x" := (# (functor_fix_snd_arg _ _ _ (monoidal_prod _) x) f)
                      (right associativity, at level 60) : monoidal_scope.
  *)

  (** *** Pentagon identity ([pentagon_identity]) *)

  (** https://ncatlab.org/nlab/show/pentagon+identity *)
  Definition pentagon_identity : UU :=
    ∏ w x y z : ob X,
      α (w ⊗ x) y z · α w x (y ⊗ z) =
      # (functor_fix_snd_arg _ _ _ (monoidal_prod mdata) z) (α w x y)
      · α w (x ⊗ y) z ·
      # (functor_fix_fst_arg _ _ _ (monoidal_prod mdata) w) (α x y z).

  (** *** Triangle identity ([pentagon_identity]) *)

  Definition triangle_identity : UU :=
    ∏ x y : ob X,
      α x 1 y · # (functor_fix_fst_arg _ _ _ (monoidal_prod mdata) x) (λ' y) =
      # (functor_fix_snd_arg _ _ _ (monoidal_prod mdata) y) (ρ' x).
End Identities.

(** *** Definition ([is_monoidal], [monoidal_category]) *)

(** A category with some monoidal data is in fact monoidal the triangle
    and pentagon identities hold. *)

Definition is_monoidal {X : category} (mdata : monoidal_data X) :=
  (pentagon_identity mdata) × (triangle_identity mdata).

Definition is_monoidal_category (X : category) : UU :=
  ∑ (mdata : monoidal_data X), is_monoidal mdata.

Definition monoidal_category : UU :=
  ∑ (X : category) (mdata : monoidal_data X), is_monoidal mdata.

(** Constructors *)
Definition mk_is_monoidal_category {X : category} (mdata : monoidal_data X)
           (pent : pentagon_identity mdata) (tri : triangle_identity mdata)
           (ismon : is_monoidal mdata) : is_monoidal_category X :=
           tpair _ mdata (dirprodpair pent tri).

Definition mk_is_monoidal {X : category} (mdata : monoidal_data X)
           (pent : pentagon_identity mdata) (tri : triangle_identity mdata) :
  is_monoidal mdata := dirprodpair pent tri.

Definition mk_monoidal_category (X : category) (mdata : monoidal_data X)
           (is : is_monoidal mdata) := tpair _ mdata is.

(** ** Cartesian monoidal categories *)

Definition cartesian_category {X : category} (bprods : BinProducts X)
           (ter : Terminal X) : is_monoidal_category X.
Proof.
  use mk_is_monoidal_category.
  - use mk_monoidal_data.
    + exact (binproduct_functor bprods).
    + exact ter.
    + use functor_iso_from_pointwise_iso.
      * use mk_nat_trans.
        { intros ?; apply binprod_assoc. }
        { intros x y f.
          unfold binprod_assoc.
          unfold binproduct_functor.
        }
      *
      apply (functor_iso_pointwise_if_iso ((X ×' X) ×' X) X (homset_property _)).
      unfold iso.
      use mk_nat_trans.
  unfold is_monoidal_category.

(** ** Symmetric monoidal categories *)
