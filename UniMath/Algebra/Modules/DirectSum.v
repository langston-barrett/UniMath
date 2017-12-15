(** Authors:
 - Langston Barrett (@siddharthist), November-December 2017
 - John Leo
 *)

Require Import UniMath.Algebra.Modules.Core.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Sets.

Section DirectSum.

Local Open Scope module.

Context {R : rng}.

(** ** Direct sums
    Direct sum of X and Y is the factor-wise module structure on the direct
    product X × Y. The inclusions and projections are given by

    - in1 :  x ↦ (x, 0)
    - in2 :  y ↦ (0, y)
    - pr1 :  (x, y) ↦ x
    - pr2 :  (x, y) ↦ y
  *)

Definition directsum_action (M : module R) (N : module R) :
  (R -> abgrdirprod M N -> abgrdirprod M N) :=
  fun r mn => dirprodpair (r * (pr1 mn)) (r * (pr2 mn)).

Definition directsum (M : module R) (N : module R) : module R.
Proof.
  unfold module.
  refine (abgrdirprod M N,, _).
  apply (@mult_to_module_struct R (abgrdirprod M N) (directsum_action M N)).
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

Notation "M ⊕ N" := (directsum M N) (at level 50) : module.
Local Open Scope module.

(** Projections *)

Definition mod_DirectSumPr1_def (M N : module R) : (M ⊕ N) -> M :=
  λ mn : M ⊕ N, dirprod_pr1 mn.

Definition mod_DirectSumPr2_def (M N : module R) : (M ⊕ N) -> N :=
  λ mn : M ⊕ N, dirprod_pr2 mn.

Lemma mod_DirectSumPr1_ismodulefun (M N : module R) :
  @ismodulefun R (M ⊕ N) M (mod_DirectSumPr1_def M N).
Proof.
  unfold ismodulefun.
  split;
    intros ? ?;
    apply idpath.
Defined.

Lemma mod_DirectSumPr2_ismodulefun (M N : module R) :
  @ismodulefun R (M ⊕ N) N (mod_DirectSumPr2_def M N).
Proof.
Proof.
  unfold ismodulefun.
  split;
    intros ? ?;
    apply idpath.
Defined.

(** Injections *)

Definition mod_DirectSumIn1_def (M N : module R) : M -> (M ⊕ N) :=
  λ m : M, dirprodpair m (unel N).

Definition mod_DirectSumIn2_def (M N : module R) : N -> (M ⊕ N) :=
  λ n : N, dirprodpair (unel M) n.

Lemma mod_DirectSumIn1_ismodulefun (M N : module R) :
  @ismodulefun R M (M ⊕ N) (mod_DirectSumIn1_def M N).
Proof.
  unfold ismodulefun.
  split.
  - intros r x.
    apply (pathsdirprod (idpath _)).
    exact (!@lunax N (unel N)).
  - intros r x.
    apply (pathsdirprod (idpath _)).
    unfold directsum_action; cbn.
    exact (!module_mult_1 r).
Defined.

Lemma mod_DirectSumIn2_ismodulefun (M N : module R) :
  @ismodulefun R N (M ⊕ N) (mod_DirectSumIn2_def M N).
Proof.
  unfold ismodulefun.
  split.
  - intros r x.
    refine (pathsdirprod _ (idpath _)).
    exact (!@runax M (unel M)).
  - intros r x.
    refine (pathsdirprod _ (idpath _)).
    unfold directsum_action; cbn.
    exact (!module_mult_1 r).
Defined.

(** Induced arrow out *)

(** TODO: refactor abgrs.v so we can use their induced arrows/proofs *)

(* Set Printing Implicit. *)
Local Open Scope multmonoid.
Local Open Scope addmonoid.
Local Open Scope module.
Definition mod_directsum_inducedarrow_out {M N O : module R}
           (f : modulefun M O) (g : modulefun N O) : modulefun (M ⊕ N) O.
Proof.
  refine ((fun x : M ⊕ N => f (pr1 x) + g (pr2 x))%addmonoid,, _).
  split.
  - intros x y.
    induction x as [x1 x2]; induction y as [y1 y2].
    induction f as [f f_is_modulefun]; induction g as [g g_is_modulefun]; cbn.
    rewrite (binopfunisbinopfun (modulefun_to_binopfun (f,, f_is_modulefun))).
    rewrite (binopfunisbinopfun (modulefun_to_binopfun (g,, g_is_modulefun))).
    unfold modulefun_to_binopfun, pr1binopfun, pr1; cbn.
    
    (** Get rid of the "(f x1) *" *)
    do 2 (rewrite (assocax (pr1module O) (f x1) _ _)).
    apply (maponpaths (fun z => (f x1) + z)%addmonoid).

    (** Get rid of the "* (g y2)" *)
    do 2 (rewrite <- (assocax (pr1module O) _ _ _)).
    apply (maponpaths (fun z => z + (g y2))%addmonoid).

    apply (commax (pr1module O) (f y1) (g x2)).
  - unfold islinear.
    intros r x; cbn.
    rewrite (modulefun_to_islinear f).
    rewrite (modulefun_to_islinear g).
    exact (!module_mult_is_ldistr r (f (pr1 x)) (g (pr2 x))).
Defined.

(** Induced arrow in *)
Definition mod_directsum_inducedarrow_in {M N O : module R}
           (f : modulefun O M) (g : modulefun O N) : modulefun O (M ⊕ N).
Proof.
  refine ((fun x : O => dirprodpair (f x) (g x)),, _).
  split.
  - intros x y.
    apply dirprodeq; cbn.
    * induction f as [f f_is_modulefun].
      apply (binopfunisbinopfun (modulefun_to_binopfun (f,, f_is_modulefun))).
    * induction g as [g g_is_modulefun].
      apply (binopfunisbinopfun (modulefun_to_binopfun (g,, g_is_modulefun))).
  - unfold islinear.
    intros r x.
    apply dirprodeq.
    * apply (modulefun_to_islinear f).
    * apply (modulefun_to_islinear g).
Defined.

Local Close Scope module.

End DirectSum.

Notation "M ⊕ N" := (directsum M N) (at level 50) : module.
