(** * The category of magmas, displayed over sets *)

(** ** Contents

  - Definitions
    - [disp_magma]: The displayed category of magmas
 *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.HLevel.

(** ** Definitions *)

Definition disp_magma : iterated_disp_precat disp_HSET.
Proof.
  use mk_disp_precat.
  - use mk_disp_cat_data.
    + use mk_disp_cat_ob_mor.
      * intro X; exact (binop (hSetpair (pr1 X) (pr2 X))).
      * intros ? ? binopX binopY f.
        exact (@isbinopfun (setwithbinoppair _ binopX)
                           (setwithbinoppair _ binopY)
                           (pr1 f)).
    + split.
      * (** TODO: upstream *)
        intros ? ?; cbn.
        use mk_isbinopfun; intros ? ?.
        reflexivity.
      * intros X Y Z f g binopX binopY binopZ isf isg.
        cbn in *.
        pose (f' := @binopfunpair (setwithbinoppair _ binopX) (setwithbinoppair _ binopY) _ isf).
        pose (g' := @binopfunpair (setwithbinoppair _ binopY) (setwithbinoppair _ binopZ) _ isg).
        exact (isbinopfuncomp f' g').
  - split; [|split; [|split]]; cbn.
    + intros ? ? ? ? ? ?; apply proofirrelevance, isapropisbinopfun.
    + intros ? ? ? ? ? ?; apply proofirrelevance, isapropisbinopfun.
    + intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
      apply proofirrelevance, isapropisbinopfun.
    + intros ? ? ? ? ? ? ?.
      apply hlevelntosn, isapropisbinopfun.
Defined.

(** ** Univalence *)

(** ** Limits *)

(** ** Colimits *)