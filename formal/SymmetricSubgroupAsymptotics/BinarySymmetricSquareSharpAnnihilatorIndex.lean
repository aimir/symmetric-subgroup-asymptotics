import SymmetricSubgroupAsymptotics.BinarySymmetricSquareSharpDualOrbit
import SymmetricSubgroupAsymptotics.BinarySymmetricSquareAnnihilatorIndex

/-! The stronger uniform dual-orbit estimate is applied to a genuine
base-field annihilator, retaining the same actual subspace and subgroup.
Its q>=4 corollary includes the field of order four without enumeration. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinarySymmetricSquareSharpAnnihilatorIndex

open BinarySymmetricSquareAction BinaryQuadraticFunctionalStabilizer
open BinarySymmetricSquareAnnihilatorIndex
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem field_mul_square_sub_one_le_two_mul_quotient_index
    [Finite F] [Finite K] [CharP K 2]
    (L : Subgroup (GeneralLinear (K := K))) (J : Submodule F (Space (K := K)))
    (hJ : ∀ A ∈ L, ∀ S ∈ J, congruenceLinearMap A S ∈ J)
    (t : K) (ht : coordinates (Pi.single (1 : Fin 3) t) ∉ J) :
    Nat.card K * (Nat.card K - 1) ^ 2 ≤
      2 * (Nat.card (Space (K := K) ⧸ J) * L.index) := by
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
  have hupper := InvariantAnnihilatorOrbitIndex.dual_orbit_card_le_quotient_card_mul_index
    (BinarySymmetricSquareDualOrbit.restrictedCongruence (F := F) (K := K))
    L J (fun A hA S hS => hJ A hA S hS) φ
  exact hlow.trans (Nat.mul_le_mul_left 2 hupper)

theorem field_square_le_quotient_card_mul_index
    [Finite F] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (L : Subgroup (GeneralLinear (K := K)))
    (J : Submodule F (Space (K := K)))
    (hJ : ∀ A ∈ L, ∀ S ∈ J, congruenceLinearMap A S ∈ J)
    (t : K) (ht : coordinates (Pi.single (1 : Fin 3) t) ∉ J) :
    Nat.card K ^ 2 ≤ Nat.card (Space (K := K) ⧸ J) * L.index := by
  have hq3 : 3 ≤ Nat.card K - 1 := by omega
  have hm := Nat.mul_le_mul_right (Nat.card K - 1) hq3
  rw [← pow_two] at hm
  have hsquare : 2 * Nat.card K ≤ (Nat.card K - 1) ^ 2 := by omega
  have hlow : 2 * Nat.card K ^ 2 ≤
      2 * (Nat.card (Space (K := K) ⧸ J) * L.index) := by
    calc
      _ = Nat.card K * (2 * Nat.card K) := by ring
      _ ≤ Nat.card K * (Nat.card K - 1) ^ 2 := Nat.mul_le_mul_left _ hsquare
      _ ≤ _ := field_mul_square_sub_one_le_two_mul_quotient_index L J hJ t ht
  exact Nat.le_of_mul_le_mul_left hlow (by decide : 0 < 2)

end SymmetricSubgroupAsymptotics.BinarySymmetricSquareSharpAnnihilatorIndex
