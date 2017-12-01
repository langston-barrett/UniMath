Add LoadPath "../" as UniMath.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Ktheory.GroupAction.

Local Open Scope cat.

(** Endomorphisms of X are arrows X --> X *)
Definition endomorphisms {C : precategory} (X : ob C) : UU := (X --> X).

(** When the hom-types of C are sets, we can form the endomorphism monoid *)
Definition endomorphism_monoid {C : category} (X : ob C) : monoid.
  refine ((((X --> X,, pr2 C X X)),, compose),, _).
  split.
  - exact (fun x x' x'' => !(@assoc C _ _ _ _ x x' x'')).
  - refine (identity X,, _).
    split.
    * exact (@id_left C X X).
    * exact (@id_right C X X).
Defined.

(** Automorphisms of X are arrows X --> X with inverses *)
Definition automorphisms {C : precategory} (X : ob C) : UU := iso X X.

(** When the hom-types of C are sets, we can form the automorphism grp *)
Definition automorphism_grp {C : category} (X : ob C) : gr.
  (* The operation is simply composition, with a proof of closure on the side *)
  pose (op := (fun f g => compose (pr1 f) (pr1 g),,
                                  @is_iso_comp_of_isos C X X X f g)).

  (* We already know that the isos form a set *)
  refine (((iso X X,, isaset_iso _ X X),, op),, _).

  unfold isgrop.
  assert (monop_iso : ismonoidop op).
  - split.
    * intros [x ?] [y ?] [z ?].
      apply eq_iso.
      unfold isassoc, op, Preamble.pr1.
      exact (!(@assoc C _ _ _ _ x y z)).
    * refine ((identity X,, identity_is_iso _ X),, _).
      split.
      +
      exact (@id_left C X X).
      + exact (@id_right C X X).

  refine ((((iso X X,, pr2 C X X)),, compose),, _).
  split.
  - exact (fun x x' x'' => !(@assoc C _ _ _ _ x x' x'')).
  - refine (identity X,, _).
    split.
    * exact (@id_left C X X).
    * exact (@id_right C X X).
Defined.