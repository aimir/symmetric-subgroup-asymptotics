import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootProductOrthogonality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAdjacentRootProducts

/-! Exact natural D root-line incidence: for distinct literal labels,
the commuting/root-product test is equivalent to meeting in a point
inside a Q-singular three-space. All fields are included. This file does
not identify the three D4 maximal-clique types or assert triality bounds. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexRootPlaneImage
open CFSGOrthogonalDIndexBundledQuadratic
variable {K : Type} [Field K]

theorem root_product_adjacency_iff (s : ℕ)
    (g h : elementaryRootGroup K (s + 4))
    (hne : conjugateRootPlane K s g ≠ conjugateRootPlane K s h) :
    (∃ x ∈ conjugateRootLine K s g, x ≠ 1 ∧
      ∃ y ∈ conjugateRootLine K s h, y ≠ 1 ∧ Commute x y ∧ IsRootElement s (x * y)) ↔
    (Module.finrank K ↥(conjugateRootPlane K s g ⊓ conjugateRootPlane K s h) = 1 ∧
      ∀ z ∈ conjugateRootPlane K s g ⊔ conjugateRootPlane K s h,
        splitQuadraticForm K (s + 4) z = 0) := by
  constructor
  · rintro ⟨x, hx, hxn, y, hy, hyn, hc, hp⟩
    obtain ⟨a, rfl⟩ := (mem_conjugateRootLine_iff_exists s g x).mp hx
    obtain ⟨b, rfl⟩ := (mem_conjugateRootLine_iff_exists s h y).mp hy
    have ha : a ≠ 0 := by
      intro ha
      apply hxn
      rw [ha, highestRoot_zero K s, mul_one, mul_inv_cancel]
    have hb : b ≠ 0 := by
      intro hb
      apply hyn
      rw [hb, highestRoot_zero K s, mul_one, mul_inv_cancel]
    exact ⟨root_product_distinct_planes_intersect_in_point s g h a b ha hb hc hp hne,
      root_product_planes_singular_sum s g h a b ha hb hc hp⟩
  · rintro ⟨hdim, hs⟩
    have hmeet : conjugateRootPlane K s g ⊓ conjugateRootPlane K s h ≠ ⊥ := by
      intro he
      have hz := congrArg (fun P : Submodule K (Index (s + 4) → K) => Module.finrank K P) he
      change Module.finrank K ↥(conjugateRootPlane K s g ⊓ conjugateRootPlane K s h) =
        Module.finrank K (⊥ : Submodule K (Index (s + 4) → K)) at hz
      rw [finrank_bot, hdim] at hz
      omega
    exact adjacent_planes_have_root_product s g h hne hmeet hs

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
