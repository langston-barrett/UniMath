(** Authors: Langston Barrett (@siddharthist), December 2017 *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Rigs_and_Rings.

Local Open Scope rig.

(** A (left) rig ideal is a submonoid that is closed under left rig multiplication *)

Section RigIdeal.

(* TODO: prove that these are propositions*)

Context .

Definition isriglideal {R : rig} (H : @submonoid (rigaddabmonoid R)) : UU :=
  ∏ (r : R) (h : H), pr1submonoid _ H (r * (pr1 h)).

Definition isrigrideal {R : rig} (H : @submonoid (rigaddabmonoid R)) : UU :=
  ∏ (r : R) (h : H), pr1submonoid _ H ((pr1 h) * r).

Definition riglideal (R : rig) := ∑ H : @submonoid (rigaddabmonoid R), isriglideal H.

Definition rigrideal (R : rig) := ∑ H : @submonoid (rigaddabmonoid R), isrigrideal H.

Definition rigideal (R : rig) :=
  ∑ H : @submonoid (rigaddabmonoid R), isriglideal H × isrigrideal H.

Ltac concat x :=
  refine (x @ _) ||
  refine (_ @ x) ||
  refine (!x @ _) ||
  refine (_ @ !x).

Definition trivial_rigideal (R : rig) : rigideal R.
  split with (trivialsubmonoid (rigaddabmonoid R)); split;
    unfold trivialsubmonoid;
    intros r ?;
    cbn in *;
    refine (hinhfun _ (pr2 h));
    intro eq_0.
  - concat (maponpaths (fun x => r * x) eq_0).
    apply rigmultx0.
  - concat (maponpaths (fun x => x * r) eq_0).
    apply rigmult0x.
Defined.

End RigIdeal.
