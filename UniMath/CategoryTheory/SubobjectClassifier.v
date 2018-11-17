(** * Subobject classifiers *)

(** ** Contents

  - Definition
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Monics.

Local Open Scope cat.

Definition subobject_classifier {C : precategory} (T : Terminal C) : UU :=
  ∑ (O : ob C) (t : C⟦T, O⟧), ∏ (X Y : ob C) (m : Monic _ X Y),
    iscontr (∑ (chi : C⟦Y, O⟧)
               (H : m · chi = TerminalArrow _ _ · t),
               isPullback _ _ _ _ H).