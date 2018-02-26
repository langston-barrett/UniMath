(** * The precategory of types

This file defines the precategory of types in a fixed universe ([type_precate])
and shows that it has all limits [].

- Author: Langston Barrett (@siddharthist)
- Date: Feb 2018
*)


(** ** Contents:

- The precategory of types (of a fixed universe) ([type_precat])
- (Co)limits
  - Colimits
  - Limits

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

(* (Co)limits *)
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Local Open Scope cat.

(** ** The precategory of types (of a fixed universe) *)

Definition type_precat : precategory.
Proof.
  use mk_precategory.
  - use tpair; use tpair.
    + exact UU.
    + exact (λ X Y, X -> Y).
    + exact (λ X, idfun X).
    + exact (λ X Y Z f g, funcomp f g).
  - repeat split; intros; apply idpath.
Defined.

(** ** (Co)limits *)

(** *** Colimits *)

Lemma InitialType : Initial type_precat.
Proof.
  apply (mk_Initial (empty : ob type_precat)).
  exact iscontrfunfromempty.
Defined.

(** *** Limits *)

Lemma TerminalType : Terminal type_precat.
Proof.
  apply (mk_Terminal (unit : ob type_precat)).
  exact iscontrfuntounit.
Defined.

Section StandardLimits.

  Context {g : graph} (d : diagram g type_precat).

  (** This is the "standard limit" from "Homotopy limits in type theory" by Jeremy
      Avigad, Chris Kapulkin, and Peter LeFanu Lumsdaine (arXiv:1304.0680v3) *)
  Definition standard_limit : UU :=
    ∑ (x : ∏ (v : vertex g), dob d v),
    ∏ (u v : vertex g) (e : edge u v), dmor d e (x u) = x v.

  (** The condition that [standard_limit] is a cone is basically a rephrasing of
      its definition. *)
  Lemma type_cone : cone d standard_limit.
    use mk_cone; cbn.
    - exact (λ n l, pr1 l n).
    - intros u v f.
      apply funextsec; intro l; unfold funcomp; cbn.
      apply (pr2 l).
  Defined.

End StandardLimits.

Section StandardLimitHomot.

  Context {g : graph} {d : diagram g type_precat} (x y : standard_limit d).

  (** A homotopy of cones *)
  Definition standard_limit_homot : UU :=
    ∑ h : pr1 x ~ pr1 y,
      ∏ (u v : vertex g) (ed : edge u v),
        (maponpaths (dmor d ed) (h u) @ (pr2 y _ _) ed = pr2 x _ _ ed @ (h v)).

  (** Such homotopies can be made into paths *)
  Lemma type_cone_homot_to_path (h : standard_limit_homot) : x = y.
  Proof.
    apply (total2_paths_f (funextsec _ _ _ (pr1 h))).

    (** transport_lemma in peterlefanulumsdaine/hott-limits/Limits1.v. *)
    assert (transport_lemma :
              ∏ p : pr1 x = pr1 y,
                transportf _ p (pr2 x) = λ u v (ed : edge u v),
                maponpaths (dmor d ed) (!(toforallpaths _ _ _ p u))
                @ pr2 x _ _ ed
                @ toforallpaths _ _ _ p v).
    {
      intros p; induction p; cbn; unfold idfun.
      do 3 (apply funextsec; intro).
      exact (!(pathscomp0rid _)).
    }
    refine (transport_lemma _ @ _).
    apply funextsec; intro u; apply funextsec; intro v; apply funextsec; intro ed.
    rewrite toforallpaths_funextsec.
    replace (pr2 y u v ed) with (idpath _ @ (pr2 y u v ed)) by reflexivity.
    refine (_ @ maponpaths (λ p, p @ _) (pathsinv0l (maponpaths _ (pr1 h u)))).
    refine (_ @ (path_assoc (! maponpaths _ _) (maponpaths _ _) _)).
    rewrite maponpathsinv0.
    apply maponpaths, pathsinv0.
    exact (pr2 h u v ed).
  Defined.
End StandardLimitHomot.

(** The canonical cone given by an arrow X → Y where Y has a cone *)

Definition into_cone_to_cone {X Y : UU} {g : graph} {d : diagram g _}
            (coneY : cone d (Y : ob type_precat)) (f : X → Y) : cone d X.
  use mk_cone.
  - intro ver.
    exact (pr1 coneY ver ∘ (f : type_precat ⟦ X, Y ⟧)).
  - intros ver1 ver2 ed; cbn.
    apply funextsec; intro x.
    apply (eqtohomot (pr2 coneY ver1 ver2 ed)).
Defined.

Section StandardLimitUP.

  Context {g : graph} {d : diagram g type_precat}.

  (** A rephrasing of the universal property: the canonical map that makes a
      cone out of a map X → L is an equivalence. *)
  Definition is_limit_cone {L} (C : cone d L) :=
    ∏ (X : UU), isweq (@into_cone_to_cone X L g d C).

  Lemma limit_universal : is_limit_cone (type_cone d).
    intro X.
    use isweq_iso.
    - intros xcone x.
      unfold standard_limit.
      use tpair.
      + exact (λ ver, pr1 xcone ver x).
      + intros ver1 ver2 ed.
        apply (toforallpaths _ _ _ (pr2 xcone _ _ _)).
    - intros f.
      apply funextfun; intro xcone.
      use total2_paths_f; cbn; [reflexivity|].
      cbn; unfold idfun.
      apply funextsec; intro ver1.
      apply funextsec; intro ver2.
      apply funextsec; intro ed.
      do 2 (rewrite toforallpaths_funextsec).
      reflexivity.
    - intro conex.
      unfold into_cone_to_cone; cbn.
      use total2_paths_f; cbn.
      + apply funextsec; intro ver1.
        apply funextsec; intro ver2.
        reflexivity.
      + cbn.
        apply funextsec; intro ver1.
        apply funextsec; intro ver2.
        apply funextsec; intro ed.
        unfold funcomp; cbn.
        cbn.
        rewrite transportf_funextfun.
      reflexivity.
      rewrite toforallpaths_funextsec.

      reflexivity.
Lemma limit_universal (D : diagram G)
: is_limit_cone (limit_graph_cone D).
Proof.
  unfold is_limit_cone. intros X.
  apply (isequiv_adjointify (inv_map_to_limit_to_graph_cone)).
  (* is_section *)
  intros tau. apply graph_cone_homot_to_path.
  unfold map_to_graph_cone, limit_graph_cone, inv_map_to_limit_to_graph_cone;
    simpl.
  unfold graph_cone_homot; simpl.
  exists (fun i y => 1). simpl.
  intros i j f x. exact (concat_p1 _ @ (concat_1p _)^).
  (* is_retraction *)
  intros k. apply path_forall. intros x. apply limit_homot_to_path.
  unfold map_to_graph_cone, limit_graph_cone, inv_map_to_limit_to_graph_cone;
    simpl.
  unfold limit_homot; simpl.
  exists (fun i => 1). simpl.
  intros i j f. exact (concat_1p _ @ (concat_p1 _)^).
Defined.
End StandardLimitUP.


(*
  Definition limfun_to_cone {A : UU} (f : A → L X π) : cone A.
    unfold cone.
    refine ( (fun n a => p (f a) n) ,, (fun n a => _)).
    unfold funcomp.
    exact (β (f a) n).
  Defined.
*)

(** The universal property of a limit.

    - Proposition 4.2.8 (limit_universal) in Avigad, Kapulkin, and Lumsdaine
    - Generalizes Lemma 10 in Ahrens, Capriotti, and Spadotti
    - Generalizes univ-iso in HoTT/M-types
 *)
Lemma standard_LimCone {g : graph} (d : diagram g type_precat) : LimCone d.
Proof.
  apply (mk_LimCone _ (standard_limit d : ob type_precat) (type_cone d)).
  intros L' L'cone.
  use iscontrpair.
  - use tpair.
    + intro l'.
      unfold standard_limit.
      use tpair.
      * exact (λ ver, pr1 L'cone ver l').
      * intros ver1 ver2 ed.
        apply (eqtohomot (pr2 L'cone ver1 ver2 ed)).
    + intro; reflexivity.
  - intro other.
    use total2_paths_f; cbn.
    +
      apply funextfun; intro l'.
      use total2_paths_f.
      Check (pr2 other).
      Check (pr2 l').
