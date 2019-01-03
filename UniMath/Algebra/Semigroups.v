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

(** [(X = Y) ≃ (binopiso X Y)]

   This is very similar to the case for sets with binary operations
   ([setwithbinop_univalence]).
 *)

Definition semigroup_univalence (X Y : semigroup) : (X = Y) ≃ (binopiso X Y).
Proof.
  apply (@weqcomp _ (pr1 X = pr1 Y)).
  - apply PartA.path_sigma_hprop, isapropisassoc.
  - exact (setwithbinop_univalence X Y).
Qed.

Definition semigroup_univalence_map (X Y : semigroup) : X = Y -> semigroupiso X Y.
Proof.
  intro e. induction e. exact (idsemigroupiso X).
Defined.

Lemma semigroup_univalence_isweq (X Y : semigroup) :
  isweq (semigroup_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (semigroup_univalence_weq1 X Y)
                   (weqcomp (semigroup_univalence_weq2 X Y) (semigroup_univalence_weq3 X Y))).
  - intros e. induction e.
    use (pathscomp0 weqcomp_to_funcomp_app).
    use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque semigroup_univalence_isweq.

Definition semigroup_univalence (X Y : semigroup) : (X = Y) ≃ (semigroupiso X Y).
Proof.
  use weqpair.
  - exact (semigroup_univalence_map X Y).
  - exact (semigroup_univalence_isweq X Y).
Defined.
Opaque semigroup_univalence.