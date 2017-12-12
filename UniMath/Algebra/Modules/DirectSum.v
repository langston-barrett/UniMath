(** Authors:
 - Langston Barrett (@siddharthist), November-December 2017
 - John Leo
 *)

Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Sets.

Local Open Scope module.

Definition directsum_action {R : rng} (M : module R) (N : module R) : 
  (R -> abgrdirprod M N -> abgrdirprod M N) :=
  fun r mn => dirprodpair (r * (pr1 mn)) (r * (pr2 mn)).

Definition directsum {R : rng} (M : module R) (N : module R) : module R.
Proof.
  unfold module.
  refine (abgrdirprod M N,, _).
  apply (@mult_to_module_struct R (abgrdirprod M N) (@directsum_action R M N)).
  - unfold mult_isldistr_wrt_grop.
    intros r [x1 x2] [y1 y2].
    apply pathsdirprod;
      apply module_mult_is_ldistr.
  - unfold mult_isrdistr_wrt_rngop1.
    intros r s [x1 x2].
    apply pathsdirprod;
      apply module_mult_is_rdistr.
  - unfold mult_isrdistr_wrt_rngop2.
    intros r s [x1 x2].
    apply pathsdirprod;
      apply module_mult_assoc.
  - unfold mult_unel.
    intros [x1 x2].
    apply pathsdirprod;
      apply module_mult_unel2.
Defined.


