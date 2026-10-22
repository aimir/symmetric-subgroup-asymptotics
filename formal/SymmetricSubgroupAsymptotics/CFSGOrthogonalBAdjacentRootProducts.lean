import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPairRootRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootPlaneMembership
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalCompanion
import SymmetricSubgroupAsymptotics.CFSGAlternatingPairComposition
import SymmetricSubgroupAsymptotics.CFSGAlternatingPairSums
import SymmetricSubgroupAsymptotics.CFSGMatrixDisplacement
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPlaneLabels

/-! Actual adjacent singular root planes supply nonidentity elements
in their SAME original root subgroups which commute and whose product
is a long root. The construction uses a common original vector and
actual pair-root words; no polar adjacency converse is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGAlternatingPairOperator
open CFSGMatrixDisplacement
variable {K : Type} [Field K] [Finite K]

theorem adjacent_planes_have_root_product (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g h : elementaryRootGroup K (s + 3))
    (hne : conjugateRootPlane (K := K) s g ≠ conjugateRootPlane (K := K) s h)
    (hmeet : conjugateRootPlane (K := K) s g ⊓ conjugateRootPlane (K := K) s h ≠ ⊥)
    (hs : IsTotallySingular (K := K) s
      (conjugateRootPlane (K := K) s g ⊔ conjugateRootPlane (K := K) s h)) :
    ∃ x ∈ conjugateRootLine h2 s g, x ≠ 1 ∧
      ∃ y ∈ conjugateRootLine h2 s h, y ≠ 1 ∧ Commute x y ∧ IsLongRootElement s (x * y) := by
  let P : Submodule K (Index (s + 3) → K) := conjugateRootPlane (K := K) s g
  let Q : Submodule K (Index (s + 3) → K) := conjugateRootPlane (K := K) s h
  have hPdim : Module.finrank K P = 2 := conjugateRootPlane_finrank s g
  have hQdim : Module.finrank K Q = 2 := conjugateRootPlane_finrank s h
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
  obtain ⟨x, hxl, hxD, hxn, hxR⟩ := exists_longRoot_with_pairOperator h2 s u v hu
    (hs u huS u huS) (hs v hvS v hvS) (hs u huS v hvS) hnv 1
  obtain ⟨y, hyl, hyD, hyn, hyR⟩ := exists_longRoot_with_pairOperator h2 s u w hu
    (hs u huS u huS) (hs w hwS w hwS) (hs u huS w hwS) hnw 1
  obtain ⟨z, hzl, hzD, hzn, hzR⟩ := exists_longRoot_with_pairOperator h2 s u (v + w) hu
    (hs u huS u huS) (hs (v + w) hvwS (v + w) hvwS)
    (hs u huS (v + w) hvwS) hnvw 1
  have hx : displacement x.val = pairOperator (gram K (s + 3)).toBilin' u v := by
    simpa only [one_smul] using hxD
  have hy : displacement y.val = pairOperator (gram K (s + 3)).toBilin' u w := by
    simpa only [one_smul] using hyD
  have hz : displacement z.val = pairOperator (gram K (s + 3)).toBilin' u (v + w) := by
    simpa only [one_smul] using hzD
  have hAC : (pairOperator (gram K (s + 3)).toBilin' u v).comp
      (pairOperator (gram K (s + 3)).toBilin' u w) = 0 :=
    pairOperator_comp_eq_zero_of_orthogonal (gram K (s + 3)).toBilin' u v w
      (hs u huS u huS) (hs v hvS u huS) (hs u huS w hwS) (hs v hvS w hwS)
  have hCA : (pairOperator (gram K (s + 3)).toBilin' u w).comp
      (pairOperator (gram K (s + 3)).toBilin' u v) = 0 :=
    pairOperator_comp_eq_zero_of_orthogonal (gram K (s + 3)).toBilin' u w v
      (hs u huS u huS) (hs w hwS u huS) (hs u huS v hvS) (hs w hwS v hvS)
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
  refine ⟨x, longRoot_mem_line_of_range h2 s g x hxl (hxn one_ne_zero)
    ((hxR one_ne_zero).trans hvspan), hxn one_ne_zero,
    y, longRoot_mem_line_of_range h2 s h y hyl (hyn one_ne_zero)
    ((hyR one_ne_zero).trans hwspan), hyn one_ne_zero, ?_, ?_⟩
  · change x * y = y * x
    exact hxy.trans hyx.symm
  · rw [hxy]
    exact hzl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
