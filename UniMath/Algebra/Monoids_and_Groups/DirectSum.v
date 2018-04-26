(** * Direct sum of abelain groups

Author: Langston Barrett (@siddharthist)
*)

(** ** Contents

- Definitions
 *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Algebra.Monoids_and_Groups.

Local Open Scope multmonoid.

Section DirectSum.

  Context {I : UU}.

  (** The operation on finite-length vectors with values in the group.

    The fact that the vectors have finite length differentiates this
    construction from the direct product.
  *)
  Definition dirsum_op (X : I → monoid) : binop (∑ n : nat, Vector (∏ i : I, X i) n).
  Proof.
    intros v1 v2.
    exists (pr1 v1 + pr1 v2).
    intros s i.
    induction (isdecrelnatlth (stntonat _ s) (pr1 v1)) as [ islt1 | nislt1 ];
      induction (isdecrelnatlth (stntonat _ s) (pr1 v2)) as [ islt2 | nislt2 ].
    - (** i < length v1 and i < length v2  *)
      pose (x1 := pr2 v1 (stnpair _ (stntonat _ s) islt1)).
      pose (x2 := pr2 v2 (stnpair _ (stntonat _ s) islt2)).
      exact (x1 i * x2 i).
    - (** i < length v1 and i ≮ length v2  *)
      exact (pr2 v1 (stnpair _ (stntonat _ s) islt1) i).
    - (** i ≮ length v1 and i < length v2  *)
      exact (pr2 v2 (stnpair _ (stntonat _ s) islt2) i).
    - (** i ≮ length v1 and i ≮ length v2  *)
      exact (unel (X i)).
  Defined.

  Local Lemma setset (X : I → monoid) : isaset (∑ n : nat, Vector (∏ i : I, X i) n).
  Proof.
    change isaset with (isofhlevel 2).
    apply isofhleveltotal2.
    - apply isasetnat.
    - do 2 (intro; apply impred).
      intro; apply setproperty.
  Defined.

  Local Lemma transportb_stn {m n : nat} (e: m=n) (i: ⟦n⟧ ) :
    transportb stn e i = stnpair m (pr1 i) (transportb (λ k, pr1 i < k) e (pr2 i)).
  Proof.
    intros; induction e.
    apply subtypeEquality_prop, idpath.
  Defined.

  Local Lemma eq_fun {X Y : UU} (f g : X → Y) (x1 x2 : X) :
    x1 = x2 → f = g → f x1 = g x2.
  Proof.
    intros eq1 eq2; induction eq1, eq2; reflexivity.
  Defined.


  Lemma ismonoidop_dirsum_op (X : I → monoid) : ismonoidop (dirsum_op X).
  Proof.
    use mk_ismonoidop.
    - intros v1 v2 v3.
      use total2_paths_f.
      + unfold dirsum_op; cbn.
        apply natplusassoc.
      +
        refine (transportf_fun _ _ (pr2 (dirsum_op X (dirsum_op X v1 v2) v3)) @ _).
        apply funextfun; intro z.
        unfold funcomp.
        refine (maponpaths _ (transportb_stn _ z) @ _).
        induction (isdecrelnatlth (stntonat _ z) (pr1 v1));
          induction (isdecrelnatlth (stntonat _ z) (pr1 v2));
          induction (isdecrelnatlth (stntonat _ z) (pr1 v3)); cbn.
        cbn.
        Set Printing All.
      (* induction (iscoantisymmnatlth (stntonat _ i) (pr1 v2)). *)
      (* + (** i < length v1 and length v2 < i *) *)
      (*   exact x1. *)
      (* + *)

End DirectSum.
