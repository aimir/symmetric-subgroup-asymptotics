import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootProductIntersection
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootProductSingularity
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootPairCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalCompanion

/-! The intrinsic commuting/root-product condition forces the sum of
the SAME original D root planes to be Q-singular in every characteristic.
The shared-axis quadratic obstruction, rather than division by two,
supplies the characteristic-two necessity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexRootPlaneImage
open CFSGOrthogonalDIndexSingularRootPlanes CFSGOrthogonalDIndexBundledQuadratic
variable {K : Type} [Field K]

theorem root_product_planes_singular_sum (s : ℕ)
    (g h : elementaryRootGroup K (s + 4)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : Commute (g * highestRoot K s a * g⁻¹) (h * highestRoot K s b * h⁻¹))
    (hp : IsRootElement s ((g * highestRoot K s a * g⁻¹) * (h * highestRoot K s b * h⁻¹))) :
    ∀ x ∈ conjugateRootPlane K s g ⊔ conjugateRootPlane K s h,
      splitQuadraticForm K (s + 4) x = 0 := by
  let P := conjugateRootPlane K s g
  let Q := conjugateRootPlane K s h
  let B := (splitQuadraticForm K (s + 4)).polarBilin
  obtain ⟨u, huPQ, hu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (root_product_planes_inf_ne_bot s g h a b ha hb hc hp)
  have huP : u ∈ P := huPQ.1
  have huQ : u ∈ Q := huPQ.2
  obtain ⟨v, hvP, hnv, hvspan⟩ := CFSGTwoDimensionalSubmoduleBasis.exists_companion P
    (conjugateRootPlane_finrank K s g) u huP hu
  obtain ⟨w, hwQ, hnw, hwspan⟩ := CFSGTwoDimensionalSubmoduleBasis.exists_companion Q
    (conjugateRootPlane_finrank K s h) u huQ hu
  obtain ⟨c, hc0, hX⟩ := root_displacement_of_spanning_pair s g a ha u v hvspan
  obtain ⟨d, hd0, hY⟩ := root_displacement_of_spanning_pair s h b hb u w hwspan
  have huQ0 := conjugateRootPlane_singular K s g u huP
  have hvQ0 := conjugateRootPlane_singular K s g v hvP
  have hwQ0 := conjugateRootPlane_singular K s h w hwQ
  have huv : B u v = 0 := conjugateRootPlane_polar_zero K s g u v huP hvP
  have huw : B u w = 0 := conjugateRootPlane_polar_zero K s h u w huQ hwQ
  have huu : B u u = 0 := conjugateRootPlane_polar_zero K s g u u huP huP
  have hvu : B v u = 0 := conjugateRootPlane_polar_zero K s g v u hvP huP
  have hex : ∃ z, B u z ≠ 0 := by
    by_contra! hz
    exact hu ((splitQuadraticForm_nondegenerate K (s + 4)).1 u hz)
  obtain ⟨z, hz⟩ := hex
  have hvw : B v w = 0 := shared_axis_root_product_forces_orthogonal s
    (g * highestRoot K s a * g⁻¹) (h * highestRoot K s b * h⁻¹)
    u v w z c d hc0 hd0 huQ0 hvQ0 hwQ0 huv huw hz hX hY hp
  have hcross : ∀ p ∈ P, ∀ q ∈ Q, B p q = 0 := by
    intro p hp q hq
    rw [← hvspan] at hp
    rw [← hwspan] at hq
    obtain ⟨e, f, rfl⟩ := Submodule.mem_span_pair.mp hp
    obtain ⟨i, j, rfl⟩ := Submodule.mem_span_pair.mp hq
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, huu, huw, hvu, hvw, mul_zero, add_zero]
  intro x hx
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
  have hsum : splitQuadraticForm K (s + 4) (p + q) =
      splitQuadraticForm K (s + 4) p + splitQuadraticForm K (s + 4) q + B p q :=
    QuadraticMap.map_add (splitQuadraticForm K (s + 4)) p q
  simpa only [conjugateRootPlane_singular K s g p hp,
    conjugateRootPlane_singular K s h q hq, hcross p hp q hq, zero_add] using hsum

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
