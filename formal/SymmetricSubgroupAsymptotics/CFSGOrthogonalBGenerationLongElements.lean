import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortMembership
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortCommutator

/-! Genuine long-root words in the actual B group in odd characteristic.
The coefficient two is inverted only in the proved matrix-value theorem;
the group element itself is an explicit commutator of actual short roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationLongElements
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationShortMembership CFSGOrthogonalBGenerationShortCommutator
variable (K : Type) [Field K]

def longRootElement (s : ℕ) (b c : Fin (s + 1) ⊕ Fin (s + 1)) (a : K) :
    elementaryRootGroup K (s + 1) :=
  ⟨shortUnit K (s + 1) b a * shortUnit K (s + 1) c (-(2 : K)⁻¹) *
      (shortUnit K (s + 1) b a)⁻¹ * (shortUnit K (s + 1) c (-(2 : K)⁻¹))⁻¹,
    (elementaryRootGroup K (s + 1)).mul_mem
      ((elementaryRootGroup K (s + 1)).mul_mem
        ((elementaryRootGroup K (s + 1)).mul_mem
          (shortUnit_mem K s b a) (shortUnit_mem K s c (-(2 : K)⁻¹)))
        ((elementaryRootGroup K (s + 1)).inv_mem (shortUnit_mem K s b a)))
      ((elementaryRootGroup K (s + 1)).inv_mem (shortUnit_mem K s c (-(2 : K)⁻¹)))⟩

theorem longRootElement_val (h2 : (2 : K) ≠ 0) (s : ℕ)
    (b c : Fin (s + 1) ⊕ Fin (s + 1)) (hbc : b ≠ c) (hbp : b ≠ paired (s + 1) c)
    (a : K) : ((longRootElement K s b c a).val : Mat K (s + 1)) =
      1 + a • longArray K (s + 1) b c := by
  have hh := short_commutator_val K (s + 1) b c hbc hbp a (-(2 : K)⁻¹)
  have hc : -2 * a * (-(2 : K)⁻¹) = a := by
    field_simp [h2]
    all_goals ring
  simpa only [longRootElement, hc] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationLongElements
