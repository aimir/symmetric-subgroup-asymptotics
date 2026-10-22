import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairRootRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootPlaneMembership
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalCompanion
import SymmetricSubgroupAsymptotics.CFSGAlternatingPairComposition
import SymmetricSubgroupAsymptotics.CFSGAlternatingPairSums
import SymmetricSubgroupAsymptotics.CFSGMatrixDisplacement

/-! Actual adjacent singular root planes supply nonidentity elements
in their SAME original root subgroups which commute and whose product
is a long root. The construction uses a common original vector and
actual pair-root words; no polar adjacency converse is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexRootPlaneImage
open CFSGOrthogonalDIndexSingularRootPlanes CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPolarForm CFSGAlternatingPairOperator
open CFSGMatrixDisplacement
variable {K : Type} [Field K]

theorem adjacent_planes_have_root_product (s : ℕ)
    (g h : elementaryRootGroup K (s + 4))
    (hne : conjugateRootPlane K s g ≠ conjugateRootPlane K s h)
    (hmeet : conjugateRootPlane K s g ⊓ conjugateRootPlane K s h ≠ ⊥)
    (hs : ∀ z ∈ conjugateRootPlane K s g ⊔ conjugateRootPlane K s h,
      splitQuadraticForm K (s + 4) z = 0) :
    ∃ x ∈ conjugateRootLine K s g, x ≠ 1 ∧
      ∃ y ∈ conjugateRootLine K s h, y ≠ 1 ∧ Commute x y ∧ IsRootElement s (x * y) := by
  let P : Submodule K (Index (s + 4) → K) := conjugateRootPlane K s g
  let Q : Submodule K (Index (s + 4) → K) := conjugateRootPlane K s h
  have hPdim : Module.finrank K P = 2 := conjugateRootPlane_finrank K s g
  have hQdim : Module.finrank K Q = 2 := conjugateRootPlane_finrank K s h
  have hsB (x : Index (s + 4) → K) (hx : x ∈ P ⊔ Q)
      (y : Index (s + 4) → K) (hy : y ∈ P ⊔ Q) :
      (splitQuadraticForm K (s + 4)).polarBilin x y = 0 := by
    change splitQuadraticForm K (s + 4) (x + y) - splitQuadraticForm K (s + 4) x -
      splitQuadraticForm K (s + 4) y = 0
    rw [hs (x + y) ((P ⊔ Q).add_mem hx hy), hs x hx, hs y hy]
    ring
  have hsplit (x : Index (s + 4) → K) (hx : x ∈ P ⊔ Q) : splitQ K x = 0 :=
    (splitQuadraticForm_apply K (s + 4) x).symm.trans (hs x hx)
  have hpolar (x : Index (s + 4) → K) (hx : x ∈ P ⊔ Q)
      (y : Index (s + 4) → K) (hy : y ∈ P ⊔ Q) : polar K x y = 0 :=
    (splitQuadraticForm_polar K (s + 4) x y).symm.trans (hsB x hx y hy)
  have hPin : P ≤ P ⊔ Q := le_sup_left
  have hQin : Q ≤ P ⊔ Q := le_sup_right
  obtain ⟨u, huPQ, hu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmeet
  have huP : u ∈ P := huPQ.1
  have huQ : u ∈ Q := huPQ.2
  obtain ⟨v, hvP, hnv, hvspan⟩ := CFSGTwoDimensionalSubmoduleBasis.exists_companion P
    hPdim u huP hu
  obtain ⟨w, hwQ, hnw, hwspan⟩ := CFSGTwoDimensionalSubmoduleBasis.exists_companion Q
    hQdim u huQ hu
  have huS : u ∈ P ⊔ Q := hPin huP
  have hvS : v ∈ P ⊔ Q := hPin hvP
  have hwS : w ∈ P ⊔ Q := hQin hwQ
  have hvwS : v + w ∈ P ⊔ Q := (P ⊔ Q).add_mem hvS hwS
  have hnvw (c : K) : v + w ≠ c • u := by
    intro he
    have hew : w = c • u - v := by rw [← he]; abel
    have hwP : w ∈ P := by
      rw [hew]
      exact P.sub_mem (P.smul_mem c huP) hvP
    have hQP : Q ≤ P := by
      rw [← hwspan]
      apply Submodule.span_le.mpr
      rintro z (hz | hz)
      · rcases hz with rfl; exact huP
      · rcases hz with rfl; exact hwP
    exact hne (Submodule.eq_of_le_of_finrank_le hQP
      (by rw [hPdim, hQdim])).symm
  obtain ⟨x, hxl, hxD, hxn, hxR⟩ := exists_root_with_pairOperator s u v hu
    (hsplit u huS) (hsplit v hvS) (hpolar u huS v hvS) hnv 1
  obtain ⟨y, hyl, hyD, hyn, hyR⟩ := exists_root_with_pairOperator s u w hu
    (hsplit u huS) (hsplit w hwS) (hpolar u huS w hwS) hnw 1
  obtain ⟨z, hzl, hzD, hzn, hzR⟩ := exists_root_with_pairOperator s u (v + w) hu
    (hsplit u huS) (hsplit (v + w) hvwS)
    (hpolar u huS (v + w) hvwS) hnvw 1
  have hx : displacement x.val = pairOperator (splitQuadraticForm K (s + 4)).polarBilin u v := by
    simpa only [one_smul] using hxD
  have hy : displacement y.val = pairOperator (splitQuadraticForm K (s + 4)).polarBilin u w := by
    simpa only [one_smul] using hyD
  have hz : displacement z.val = pairOperator (splitQuadraticForm K (s + 4)).polarBilin u (v + w) := by
    simpa only [one_smul] using hzD
  have hAC : (pairOperator (splitQuadraticForm K (s + 4)).polarBilin u v).comp
      (pairOperator (splitQuadraticForm K (s + 4)).polarBilin u w) = 0 :=
    pairOperator_comp_eq_zero_of_orthogonal (splitQuadraticForm K (s + 4)).polarBilin u v w
      (hsB u huS u huS) (hsB v hvS u huS) (hsB u huS w hwS) (hsB v hvS w hwS)
  have hCA : (pairOperator (splitQuadraticForm K (s + 4)).polarBilin u w).comp
      (pairOperator (splitQuadraticForm K (s + 4)).polarBilin u v) = 0 :=
    pairOperator_comp_eq_zero_of_orthogonal (splitQuadraticForm K (s + 4)).polarBilin u w v
      (hsB u huS u huS) (hsB w hwS u huS) (hsB u huS v hvS) (hsB w hwS v hvS)
  have hxy : x * y = z := by
    apply Subtype.ext
    apply displacement_injective
    change displacement (x.val * y.val) = displacement z.val
    rw [displacement_mul, hx, hy, hAC, add_zero, hz, pairOperator_add_right]
  have hyx : y * x = z := by
    apply Subtype.ext
    apply displacement_injective
    change displacement (y.val * x.val) = displacement z.val
    rw [displacement_mul, hy, hx, hCA, add_zero, hz, pairOperator_add_right]
    exact add_comm _ _
  refine ⟨x, root_mem_line_of_range s g x hxl (hxn one_ne_zero)
    ((hxR one_ne_zero).trans hvspan), hxn one_ne_zero,
    y, root_mem_line_of_range s h y hyl (hyn one_ne_zero)
    ((hyR one_ne_zero).trans hwspan), hyn one_ne_zero, ?_, ?_⟩
  · change x * y = y * x
    exact hxy.trans hyx.symm
  · rw [hxy]
    exact hzl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootDisplacements
