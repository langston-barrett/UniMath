Add LoadPath "../../" as UniMath.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.Algebra.Monoids_and_Groups.

Section Commutator.
  Variable (G : gr).

  Local Notation "g ^-1" := (grinv G g) (at level 50).
  Local Open Scope multmonoid_scope.

  Definition commutator (g h : G) : G := g^-1 * h^-1 * g * h.

  (* Definition abgr_kernel_hsubtype {A B : abgr} (f : monoidfun A B) : hsubtype A := *)
  (*   (fun x : A => ishinh ((f x) = unel B)). *)

  Definition commutator_subtype : hsubtype G :=
    fun g => ∃ (g' g'' : G), g = (commutator g' g'').

  Theorem commutator_subgr_is_subgr : issubgr commutator_subtype.
    split.
    { (* Closed under the group composition *)
      split.
      {
        intros [g g_in_commutator] [h h_in_commutator].
        unfold commutator_subtype, pr1 in *.
        simpl in g_in_commutator, h_in_commutator.
        apply g_in_commutator; intros [g1 [g2 g_is_commutator]].
        apply h_in_commutator; intros [h1 [h2 h_is_commutator]].
        unfold commutator in *.
      }
      {

      }
    }
    { (* Closed under inversion *)
    }
  Qed.

