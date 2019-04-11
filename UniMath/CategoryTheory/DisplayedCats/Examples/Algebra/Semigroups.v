(** * The category of semigroups, displayed over sets *)

(** ** Contents

  - Definitions
    - [disp_semigroup]: The displayed category of semigroups
  - Univalence
  - Limits
  - Colimits
 *)

Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Semigroups.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.HLevel.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Algebra.SetWithBinOp.

(** ** Definitions *)

Definition disp_semigroup : iterated_disp_precat disp_magma.
Proof.
  use mk_disp_precat.
  - use mk_disp_cat_data.
    + use mk_disp_cat_ob_mor.
      * intro m; exact (isassoc (pr2 m)).
      * (** These are just [binopfun]. *)
        intros ? ? ? ?; exact (fun _ => unit).
    + (** TODO: make a constructor for this trivial case. *)
      split.
      * intros ? ?; exact tt.
      * intros ? ? ? ? ? ? ? ? ? ?; exact tt.
  - split; [|split; [|split]]; cbn.
    + intros ? ? ? ? ? ?; apply isProofIrrelevantUnit.
    + intros ? ? ? ? ? ?; apply isProofIrrelevantUnit.
    + intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?;
      apply isProofIrrelevantUnit.
    + intros ? ? ? ? ? ? ?.
      do 2 (apply hlevelntosn).
      apply iscontrunit.
Defined.

(** The objects are indeed semigroups. *)
Lemma ob_disp_semigroup :
  ob (total_precategory disp_semigroup) ≃ semigroup.
Proof.
  unfold total_precategory, disp_semigroup, semigroup; cbn.
  unfold setwithbinop.
  unfold hSet.
  eapply weqcomp; [apply weqtotal2asstor|].
  apply invweq; eapply weqcomp; [apply weqtotal2asstor|].
  apply idweq.
Defined.

(** ** Univalence *)

(** ** Limits *)

(** ** Colimits *)