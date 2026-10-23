import SymmetricSubgroupAsymptotics.CFSGOrthogonalDQuadraticPairTail
import SymmetricSubgroupAsymptotics.CFSGTwistedDTailTwist

/-! The first-pair stabilizer in the actual defining-fixed quadratic
matrix group is a literal smaller defining-fixed quadratic group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticPairTail
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexQuadraticForm CFSGTwistedDNaturalFieldTwist

theorem exists_fixed_quadratic_tail (K : Type) [Field K] (n : ℕ) (σ : K ≃+* K)
    (u : (Mat K (n + 3))ˣ) (hQ : u ∈ quadraticPreserving K (n + 3))
    (ht : unitTwist K (n + 1) σ u = u)
    (hp : (u : Mat K (n + 3)) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (hn : (u : Mat K (n + 3)) *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1) :
    ∃ a : quadraticPreserving K (n + 2),
      tailUnitHom K (n + 2) a.val = u ∧ unitTwist K n σ a.val = a.val := by
  obtain ⟨a, ha⟩ := CFSGOrthogonalDQuadraticPairTail.exists_quadratic_tail K (n + 2) u hQ hp hn
  refine ⟨a, ha, ?_⟩
  apply CFSGTwistedDTailTwist.fixed_tail_of_fixed_extension K n σ a.val
  rw [ha]
  exact ht

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticPairTail
