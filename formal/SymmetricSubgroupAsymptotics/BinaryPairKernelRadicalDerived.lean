import SymmetricSubgroupAsymptotics.BinaryPairJointNormalFBounds
import SymmetricSubgroupAsymptotics.BinaryPairLiftCarryExponent
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation

/-! The relative radical of the actual elementary pair kernel belongs to
the original derived group, with no abelianization saturation assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem kernel_relativeRadical_le_derived :
    primeRelativeRadical 2 F.top.ker ≤ commutator U := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [primeRelativeRadical_eq_powerCommutator, primeRelativePowerCommutator]
  apply sup_le
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨n, rfl⟩
    change (n : U) ^ 2 ∈ commutator U
    rw [F.physical_kernel_pow_two n]
    exact (commutator U).one_mem
  · simpa only [commutator_def] using
      (Subgroup.commutator_mono (show F.top.ker ≤ ⊤ from le_top) le_rfl)

theorem radical_coordinate_le_derived
    (R : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = R) :
    F.coordinateSubgroup R ≤ commutator U := by
  rw [← hR, F.coordinateSubgroup_ambientAxis]
  exact inf_le_right.trans F.kernel_relativeRadical_le_derived

end SymmetricSubgroupAsymptotics.BinaryPairFrame
