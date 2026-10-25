import SymmetricSubgroupAsymptotics.AbelianJointMotionFibres
import SymmetricSubgroupAsymptotics.AbelianActionClassBound
import SymmetricSubgroupAsymptotics.AbelianExtensionClassComparison
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact joint-motion class capacity for a split abelian action, and its
upper bound for an ORIGINAL nonsplit abelian extension. Every summand
retains the SAME two commuting quotient elements and the SAME kernel.
No full-base enlargement, independent maximum or splitting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AbelianExtensionJointMotionClassBound
open AbelianActionClassBound AbelianJointMotionFibres

variable {N H : Type*} [CommGroup N] [Group H] [Finite H]

def jointCapacity (φ : H →* MulAut N) : ℕ :=
  letI : Fintype (CommutingPairs H) := Fintype.ofFinite _
  ∑ t : CommutingPairs H, (jointMotion φ t.val.1 t.val.2).range.index

theorem split_class_card_mul_complement_eq [Finite N] (φ : H →* MulAut N) :
    Nat.card H * Nat.card (ConjClasses (N ⋊[φ] H)) = jointCapacity φ := by
  letI : Fintype (CommutingPairs H) := Fintype.ofFinite _
  have hc : Nat.card (CommutingPairs (N ⋊[φ] H)) = Nat.card N * jointCapacity φ := by
    calc
      Nat.card (CommutingPairs (N ⋊[φ] H)) =
          Nat.card ((t : CommutingPairs H) ×
            AbelianActionCommutingFibreBound.Fibre φ t.val.1 t.val.2) :=
        Nat.card_congr (commutingEquiv φ)
      _ = ∑ t : CommutingPairs H,
          Nat.card (AbelianActionCommutingFibreBound.Fibre φ t.val.1 t.val.2) :=
        Nat.card_sigma
      _ = ∑ t : CommutingPairs H,
          Nat.card N * (jointMotion φ t.val.1 t.val.2).range.index := by
        apply Finset.sum_congr rfl
        intro t _
        exact commuting_fibre_card φ t.val.1 t.val.2 t.property
      _ = Nat.card N * jointCapacity φ := (Finset.mul_sum _ _ _).symm
  rw [card_comm_eq_card_conjClasses_mul_card, SemidirectProduct.card] at hc
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := N))
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hc

variable {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]

/-- The capacity uses the actual quotient conjugation of the original
normal subgroup. The commutative group instance changes no operation. -/
def extensionJointCapacity : ℕ := by
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := mul_comm' }
  exact jointCapacity (AbelianExtensionConjugation.quotientConjugation A)

theorem class_card_mul_quotient_le :
    Nat.card (G ⧸ A) * Nat.card (ConjClasses G) ≤ extensionJointCapacity A := by
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := mul_comm' }
  change Nat.card (G ⧸ A) * Nat.card (ConjClasses G) ≤
    jointCapacity (AbelianExtensionConjugation.quotientConjugation A)
  exact (Nat.mul_le_mul_left (Nat.card (G ⧸ A))
    (AbelianExtensionClassComparison.class_card_le_associated_split A)).trans_eq
      (split_class_card_mul_complement_eq
        (AbelianExtensionConjugation.quotientConjugation A))

end SymmetricSubgroupAsymptotics.AbelianExtensionJointMotionClassBound
