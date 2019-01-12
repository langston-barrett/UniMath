(** * Semigroups *)

(** * Contents

 - Semigroups
  - Basic definitions
  - Trivial (unit) semigroup
  - Homomorphisms
  - Univalence
*)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Export UniMath.Algebra.BinaryOperations.

(** ** Semigroups *)


(** ***  Basic definitions *)

Definition semigroup : UU := ∑ X : setwithbinop, isassoc (@op X).

Definition make_semigroup (X : setwithbinop) (H : isassoc (@op X)) : semigroup :=
  tpair _ X H.

Definition setwithbinop_from_semigroup : semigroup -> setwithbinop := @pr1 _ _.
Coercion setwithbinop_from_semigroup : semigroup >-> setwithbinop.

Definition isasetsemigroup (X : semigroup) : isaset X := pr2 (pr1 (pr1 X)).

Delimit Scope semigroup_scope with semigroup.
Delimit Scope addsemigroup_scope with addsemigroup.

Notation "x * y" := (op x y) : semigroup_scope.

Module AddNotation.
  Notation "x + y" := (op x y) : addsemigroup_scope.
End AddNotation.

(* To get additive notation in a file that uses this one, insert the following command:
   Import UniMath.Algebra.Semigroups.AddNotation.
*)

(** *** Trivial (unit) semigroup *)

Definition unitsemigroup : semigroup.
Proof.
  use make_semigroup.
  - use setwithbinoppair.
    + eapply hSetpair.
      exact isasetunit.
    + exact (fun x y => x).
  - abstract (intros ? ? ?; apply isProofIrrelevantUnit).
Defined.

(** *** Homomorphisms *)

(** These are just [binopfun], so there's not much to say here.
    Look in BinaryOperations.v. *)

(** *** Univalence *)

(** **** General lemma *)

(** If [T] is some class of algebraic structures which are known to be "univalent"
    in the sense that there is a family [iso : T -> T -> UU] such that for all
    [A B : T], [A = B ≃ iso A B], and [P] is a proposition that holds of certain
    [A : T], (and which is preserved under all [T]-maps), then the class of [∑ T, P]
    structures is "univalent".
 *)

(** Examples:
    - Univalence for semigroups (below) is given by taking [T] the class of sets
      with binary opertions and [P] the proposition "is associative".
    - Univalence for monoids is given by taking [T] the class of semigroups
      and [P] the proposition "is unital".
    - Univalence for commutative monoids is given by taking [T] the class of
      monoids and [P] the proposition "is commutative".
 *)

Section UnivalencePropLemma.
  Context {T : UU} {iso : T -> T -> UU}.
  Context (univalentT : ∏ A B : T, (A = B) ≃ (iso A B)).

  Lemma univalence_of_prop_structures
        (prop : T -> UU) (isaprop_prop : ∏ t, isaprop (prop t)) :
    ∏ A B : total2 prop, (A = B) ≃ (iso (pr1 A) (pr1 B)).
  Proof.
    intros A B.
    apply (@weqcomp _ (pr1 A = pr1 B)).
    - apply PartA.path_sigma_hprop.
      apply isaprop_prop.
    - apply univalentT.
  Defined.

End UnivalencePropLemma.

(** **** Univalence for semigroups *)

(** [(X = Y) ≃ (binopiso X Y)]

   This is very similar to the case for sets with binary operations
   ([setwithbinop_univalence]).
 *)

(** A proof with the "wrong" map *)
Definition semigroup_univalence' (X Y : semigroup) : (X = Y) ≃ (binopiso X Y).
Proof.
  apply (univalence_of_prop_structures setwithbinop_univalence
                                       (fun X => isassoc op)).
  intro; apply isapropisassoc.
Defined.

(** The "right" map *)
Definition semigroup_univalence_map (X Y : semigroup) : X = Y -> binopiso X Y.
Proof.
  intro e; induction e; exact (idbinopiso _).
Defined.

(** The "right" map is a weak equivalence because it is homotopic to the
    "wrong" one. *)
Lemma semigroup_univalence_isweq (X Y : semigroup) :
  isweq (semigroup_univalence_map X Y).
Proof.
  use isweqhomot.
  - apply semigroup_univalence'.
  - intros e; induction e; reflexivity.
  - use weqproperty.
Qed.
Opaque semigroup_univalence_isweq.

Definition semigroup_univalence (X Y : semigroup) : (X = Y) ≃ (binopiso X Y).
Proof.
  use weqpair.
  - exact (semigroup_univalence_map X Y).
  - exact (semigroup_univalence_isweq X Y).
Qed.
Opaque semigroup_univalence.