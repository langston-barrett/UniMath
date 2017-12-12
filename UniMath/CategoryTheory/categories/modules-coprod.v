(** Authors:
 - John Leo
 - Langston Barrett (@siddharthist), December 2017 *)

Add LoadPath "../../" as UniMath.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Modules.
Require Import UniMath.Algebra.Modules.DirectSum.
Require Import UniMath.CategoryTheory.categories.modules.

(** * Additive structure on the category of R-modules
   - Direct sums
   - Additive category structure
 *)
Section mod_coprod.

  Context {R : rng}.

  (** ** Direct sums
     Direct sum of X and Y is the factor-wise module structure on the direct
     product X × Y. The inclusions and projections are given by 
     - In1 :  x ↦ (x, 0)
     - In2 :  y ↦ (0, y)
     - Pr1 :  (x, y) ↦ x
     - Pr2 :  (x, y) ↦ y

     These define a categorical biproduct, and make the category of modules
     into an additive category.
   *)
  Local Open Scope module.
  Local Open Scope cat.
  Local Open Scope multmonoid.

  Definition mod_DirectSumIn1_def (M N : module R) : M -> (M ⊕ N) :=
    λ m : M, dirprodpair m (unel N).

  Lemma mod_DirectSumIn1_ismodulefun (M N : module R) :
    @ismodulefun R M (M ⊕ N) (mod_DirectSumIn1_def M N).
  Proof.
    unfold ismodulefun.
    split.
    - intros r x.
      apply (pathsdirprod (idpath _)).
      exact (!@lunax N 1).
    - intros r x.
      apply (pathsdirprod (idpath _)).
      unfold directsum_action; cbn.
      exact (!module_mult_1 r).
  Defined.

  Definition mod_DirectSumIn1 (M N : module R) : mod_category⟦M, M ⊕ N⟧ :=
    (mod_DirectSumIn1_def M N,, mod_DirectSumIn1_ismodulefun M N).

  Definition mod_DirectSumIn2_def (M N : module R) : N -> (M ⊕ N) :=
    λ n : N, dirprodpair (unel M) n.

  Lemma mod_DirectSumIn2_ismodulefun (M N : module R) :
    @ismodulefun R N (M ⊕ N) (mod_DirectSumIn2_def M N).
  Proof.
    unfold ismodulefun.
    split.
    - intros r x.
      refine (pathsdirprod _ (idpath _)).
      exact (!@runax M 1).
    - intros r x.
      refine (pathsdirprod _ (idpath _)).
      unfold directsum_action; cbn.
      exact (!module_mult_1 r).
  Defined.

  Definition mod_DirectSumIn2 (M N : module R) : mod_category⟦N, M ⊕ N⟧ :=
    (mod_DirectSumIn2_def M N,, mod_DirectSumIn2_ismodulefun M N).

  Local Notation "g ∘ f" := (modulefun_comp f g) (at level 50, left associativity) : functions.

End mod_coprod.
