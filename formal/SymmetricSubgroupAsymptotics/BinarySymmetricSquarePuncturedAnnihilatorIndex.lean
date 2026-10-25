import SymmetricSubgroupAsymptotics.BinarySymmetricSquareSharpAnnihilatorIndex
import SymmetricSubgroupAsymptotics.PuncturedAnnihilatorScalarWordIndex
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! An off-diagonal detecting functional is nonzero, so its actual
GL2-congruence orbit lies in the punctured annihilator. The arbitrary
prime-field subspace J and SAME projected L remain literal. A small
integer-power companion pays the four-element-field source index24. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySymmetricSquarePuncturedAnnihilatorIndex
open BinarySymmetricSquareAction BinaryQuadraticFunctionalStabilizer
open BinarySymmetricSquareAnnihilatorIndex
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem field_mul_square_sub_one_le_two_mul_punctured_quotient_index
    [Finite F] [Finite K] [CharP K 2]
    (L : Subgroup (GeneralLinear (K := K))) (J : Submodule F (Space (K := K)))
    (hJ : ∀ A ∈ L, ∀ S ∈ J, congruenceLinearMap A S ∈ J)
    (t : K) (ht : coordinates (Pi.single (1 : Fin 3) t) ∉ J) :
    Nat.card K * (Nat.card K - 1) ^ 2 ≤
      2 * ((Nat.card (Space (K := K) ⧸ J)-1) * L.index) := by
  letI : Module.Finite F (Space (K := K)) := Module.Finite.of_finite
  obtain ⟨φ, hφ⟩ := InvariantAnnihilatorOrbitIndex.exists_annihilator_nonzero_on
    J (coordinates (Pi.single (1 : Fin 3) t)) ht
  have hf : centralRestriction φ.val ≠ 0 := by
    intro he
    have hz := congrArg (fun f : Module.Dual F K => f t) he
    change φ.val (coordinates (Pi.single (1 : Fin 3) t)) = 0 at hz
    exact hφ hz
  obtain ⟨a, c, heq⟩ := exists_normalized_coefficients φ.val hf
  have hlow : Nat.card K * (Nat.card K - 1) ^ 2 ≤ 2 * Nat.card
      (InvariantAnnihilatorOrbitIndex.dualOrbit
        (BinarySymmetricSquareDualOrbit.restrictedCongruence (F := F) (K := K)) φ.val) := by
    rw [heq]
    exact BinarySymmetricSquareSharpDualOrbit.field_mul_square_sub_one_le_two_mul_dual_orbit
      (centralRestriction φ.val) hf a 1 c one_ne_zero
  have hφ0 : φ.val ≠ 0 := by
    intro he
    exact hφ (by rw [he]; rfl)
  have hupper := PuncturedAnnihilatorScalarWordIndex.dual_orbit_card_le_punctured_quotient_card_mul_index
    (BinarySymmetricSquareDualOrbit.restrictedCongruence (F := F) (K := K))
    L J (fun A hA S hS => hJ A hA S hS) φ hφ0
  exact hlow.trans (Nat.mul_le_mul_left 2 hupper)

theorem twentyFour_le_binary_multiple (k l : ℕ) (hl : 0 < l)
    (horbit : 18 ≤ (2^k-1)*l) : 24 ≤ 2^k*l := by
  by_cases hk : 5 ≤ k
  · exact ((by decide : 24 ≤ (2:ℕ)^5).trans
      (Nat.pow_le_pow_right (by decide) hk)).trans
        (Nat.le_mul_of_pos_right _ hl)
  · have hk4 : k ≤ 4 := by omega
    interval_cases k <;> norm_num at horbit <;> omega

end SymmetricSubgroupAsymptotics.BinarySymmetricSquarePuncturedAnnihilatorIndex
