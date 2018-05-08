(** * Ideals

Author: Langston Barrett (@siddharthist)
*)

(** ** Contents

- Definitions
  - Left ideals ([lideal])
  - Right ideals ([rideal])
  - Two-sided ideals ([ideal])
  - The above notions coincide for commutative rigs
- Kernel ideal
 *)

Require Import UniMath.Algebra.RigsAndRings.

Local Open Scope ring.
Local Open Scope rig.

Section Definitions.
  Context {R : rig}.

  (** *** Left ideals ([lideal]) *)

  Definition is_lideal (S : subabmonoid (rigaddabmonoid R)) : hProp.
  Proof.
    use hProppair.
    - exact (∏ (r : R) (s : R), S s → S (r * s)).
    - do 3 (apply impred; intro).
      apply propproperty.
  Defined.

  Definition lideal : UU := ∑ S : subabmonoid (rigaddabmonoid R), is_lideal S.

  Definition mk_lideal :
    ∏ (S : subabmonoid (rigaddabmonoid R)), is_lideal S → lideal := tpair _.
  Definition lideal_to_subabmonoid (I : lideal) : subabmonoid (rigaddabmonoid R) := pr1 I.
  Coercion lideal_to_subabmonoid : lideal >-> subabmonoid.

  Definition lideal_mult (LI : lideal) (x : R) (y : LI) : LI.
  Proof.
    use tpair.
    - exact (x * pr1carrier LI y).
    - apply (pr2 LI x).
      exact (pr2 y).
  Defined.

  (** *** Right ideals ([rideal]) *)

  Definition is_rideal (S : subabmonoid (rigaddabmonoid R)) : hProp.
  Proof.
    use hProppair.
    - exact (∏ (r : R) (s : R), S s → S (s * r)).
    - do 3 (apply impred; intro).
      apply propproperty.
  Defined.

  Definition rideal : UU := ∑ S : subabmonoid (rigaddabmonoid R), is_rideal S.

  Definition mk_rideal :
    ∏ (S : subabmonoid (rigaddabmonoid R)), is_rideal S → rideal := tpair _.
  Definition rideal_to_subabmonoid (I : rideal) : subabmonoid (rigaddabmonoid R) := pr1 I.
  Coercion rideal_to_subabmonoid : rideal >-> subabmonoid.

  Definition rideal_mult (RI : rideal) (y : RI) (x : R) : RI.
  Proof.
    use tpair.
    - exact (pr1carrier RI y * x).
    - apply (pr2 RI x).
      exact (pr2 y).
  Defined.

  (** *** Two-sided ideals ([ideal]) *)

  Definition is_ideal (S : subabmonoid (rigaddabmonoid R)) : hProp :=
    hconj (is_lideal S) (is_rideal S).

  Definition ideal : UU := ∑ S : subabmonoid (rigaddabmonoid R), is_ideal S.

  Definition ideal_to_subabmonoid (I : ideal) : subabmonoid (rigaddabmonoid R) := pr1 I.
  Coercion ideal_to_subabmonoid : ideal >-> subabmonoid.
  Definition ideal_to_lideal (I : ideal) : lideal :=
    mk_lideal I (dirprod_pr1 (pr2 I)).
  Coercion ideal_to_lideal : ideal >-> lideal.
  Definition ideal_to_rideal (I : ideal) : rideal :=
    mk_rideal I (dirprod_pr2 (pr2 I)).
  Coercion ideal_to_rideal : ideal >-> rideal.

  Definition mk_ideal (S : subabmonoid (rigaddabmonoid R))
             (isl : is_lideal S) (isr : is_rideal S) : ideal :=
    tpair _ S (dirprodpair isl isr).

  Definition ideal_mult_l (I : ideal) (x : R) (y : I) : I.
  Proof.
    use tpair.
    - exact (x * pr1carrier I y).
    - apply (dirprod_pr1 (pr2 I) x).
      exact (pr2 y).
  Defined.

  Definition ideal_mult_r (I : ideal) (y : I) (x : R) : I.
  Proof.
    use tpair.
    - exact (pr1carrier I y * x).
    - apply (dirprod_pr2 (pr2 I) x).
      exact (pr2 y).
  Defined.

  (** Zero is in every ideal. *)
  Lemma zero_in_ideal (I : ideal) : I.
  Proof.
    use tpair.
    - exact 0.
    - exact (pr2 (pr2 (ideal_to_subabmonoid I))).
  Defined.

  (** Elements of an ideal are not equal to 0 if and only if they are
      in the original rig. *)
  Lemma neq_zero_in_ideal (I : ideal) (x : I) :
    (x != zero_in_ideal I) ≃ (pr1carrier I x != 0).
  Proof.
    apply weqimplimpl.
    - intros neq eq.
      apply neq.
      apply subtypeEquality'.
      + assumption.
      + apply propproperty.
    - intros neq eq.
      apply neq.
      exact (maponpaths pr1 eq).
    - apply isapropneg.
    - apply isapropneg.
  Defined.
End Definitions.

Arguments lideal _ : clear implicits.
Arguments rideal _ : clear implicits.
Arguments ideal _ : clear implicits.

(** *** The above notions for commutative rigs *)

Lemma commrig_ideals (R : commrig) (S : subabmonoid (rigaddabmonoid  R)) :
  is_lideal S ≃ is_rideal S.
Proof.
  apply weqimplimpl.
  - intros islid r s ss.
    use transportf.
    + exact (S (r * s)).
    + exact (maponpaths S (rigcomm2 _ _ _)).
    + apply (islid r s ss).
  - intros isrid r s ss.
    use transportf.
    + exact (S (s * r)).
    + exact (maponpaths S (rigcomm2 _ _ _)).
    + apply (isrid r s ss).
  - apply propproperty.
  - apply propproperty.
Defined.

Corollary commrig_ideals' (R : commrig) : lideal R ≃ rideal R.
Proof.
  apply weqfibtototal; intro; apply commrig_ideals.
Defined.

(** ** Kernel ideal *)

(** The kernel of a rig homomorphism is a two-sided ideal. *)
Definition kernel_ideal {R S : rig} (f : rigfun R S) : @ideal R.
Proof.
  use mk_ideal.
  - use submonoidpair.
    + exact (@monoid_kernel_hsubtype (rigaddabmonoid R) (rigaddabmonoid S)
                                      (rigaddfun f)).
    + (** This does, in fact, describe a submonoid *)
      apply kernel_issubmonoid.
  - (** It's closed under × from the left *)
    intros r s ss; cbn in *.
    refine (monoidfunmul (rigmultfun f) _ _ @ _); cbn.
    refine (maponpaths _ ss @ _).
    refine (rigmultx0 _ (pr1 f r) @ _).
    reflexivity.
  - intros r s ss; cbn in *.
    refine (monoidfunmul (rigmultfun f) _ _ @ _); cbn.
    abstract (rewrite ss; refine (rigmult0x _ (pr1 f r) @ _); reflexivity).
Defined.
