import SymmetricSubgroupAsymptotics.BinaryPairLiftCarryExponent
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation

/-! The radical of the SAME elementary normal intersection belongs to
the full original mixed commutator cut. No equality with that cut is
asserted: genuine extra mixed bits remain available. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem intersection_relativeRadical_le_actual_commutator
    (E : Subgroup U) [E.Normal] :
    primeRelativeRadical 2 (E ⊓ F.top.ker) ≤
      ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker := by
  letI intersectionRelativeRadicalCut_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := E ⊓ F.top.ker
  have hA : A ≤ F.top.ker := inf_le_right
  rw [primeRelativeRadical_eq_powerCommutator, primeRelativePowerCommutator]
  apply sup_le
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨a, rfl⟩
    change (a : U) ^ 2 ∈ ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker
    rw [F.physical_kernel_pow_two ⟨a.val, hA a.property⟩]
    exact Subgroup.one_mem _
  · exact le_inf (Subgroup.commutator_mono (show A ≤ E from inf_le_left) le_rfl)
      ((Subgroup.commutator_le_left A ⊤).trans hA)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
