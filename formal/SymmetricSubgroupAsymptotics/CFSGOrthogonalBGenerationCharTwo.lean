import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoEquivalence
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryGeneration
import SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryGeneration
import SymmetricSubgroupAsymptotics.CFSGSymplecticLargeFieldGeneration
import SymmetricSubgroupAsymptotics.CFSGTwoGenerationBasic

/-! Actual natural B two-generation in characteristic two and every
rank at least three, transported through the proved literal restriction
equivalence. This does not identify the original projective Serre model
with a classical group by its name. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwo
open CFSGGeneration
variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem symplectic_twoGenerated (r : ℕ) (hr : 3 ≤ r) :
    TwoGenerated (CFSGSymplecticSerreMatrices.elementaryRootGroup K r) := by
  suffices hp : ∃ x y : CFSGSymplecticSerreMatrices.elementaryRootGroup K r,
      Subgroup.closure ({x, y} : Set (CFSGSymplecticSerreMatrices.elementaryRootGroup K r)) = ⊤ by
    obtain ⟨x, y, hxy⟩ := hp
    exact ⟨{x, y}, by simpa only [Finset.coe_insert, Finset.coe_singleton] using hxy,
      Finset.card_le_two⟩
  by_cases htwo : Nat.card K = 2
  · obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 3 := ⟨r - 3, by omega⟩
    exact CFSGSymplecticBinaryGeneration.elementary_exists_generating_pair htwo s
  · by_cases hthree : Nat.card K = 3
    · obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 2 := ⟨r - 2, by omega⟩
      exact CFSGSymplecticTernaryGeneration.elementary_exists_generating_pair hthree s
    · have hfour : 4 ≤ Nat.card K := by
        have hc := Finite.one_lt_card (α := K)
        omega
      obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 2 := ⟨r - 2, by omega⟩
      exact CFSGSymplecticSerreMatrices.elementary_large_field_exists_generating_pair K hfour s

theorem elementary_twoGenerated (r : ℕ) (hr : 3 ≤ r) :
    TwoGenerated (CFSGOrthogonalBSerreMatrices.elementaryRootGroup K r) :=
  of_mulEquiv (CFSGOrthogonalBGenerationCharTwoEquivalence.elementaryEquiv K r).symm
    (symplectic_twoGenerated K r hr)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwo
