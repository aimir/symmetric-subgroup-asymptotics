import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankNegativeSupport
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankForkClear

/-! Literal relative-root words clear the terminal conjugate pair in
every actual relative rank at least three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankZeroLastReduction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGSerreOrdinaryTwists CFSGTwistedDNaturalQuadraticTwist
open CFSGOrthogonalDIndexBundledQuadratic CFSGTwistedDRelativeElementaryGroup

theorem exists_clear_last_pair (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (n + 3) v = 0) (hv0 : v ≠ 0) :
    ∃ u : relativeRootGroup (n + 1) q,
      ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
        (Sum.inl (last (n + 1))) = 0 ∧
      ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
        (Sum.inr (last (n + 1))) = 0 := by
  obtain ⟨a, ha⟩ := CFSGTwistedDAllRankNegativeSupport.exists_negative_support n q v hv hQ hv0
  let w := (a.val : Mat (q.Extension 2) (n + 3)) *ᵥ v
  have hw : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) w = w :=
    CFSGTwistedDAllRankPivots.preserves_fixed n q a v hv
  obtain ⟨b, hb, hbf⟩ := CFSGTwistedDAllRankPivots.exists_negative_pivot n q w hw ha
  let x := (b.val : Mat (q.Extension 2) (n + 3)) *ᵥ w
  have hbn : x (Sum.inr (pen (n + 1))) ≠ 0 := by
    change ((b.val : Mat (q.Extension 2) (n + 3)) *ᵥ w)
      (Sum.inr (pen (n + 1))) ≠ 0
    rw [hb]
    exact one_ne_zero
  obtain ⟨c, _, hcp, hcn, _⟩ :=
    CFSGTwistedDAllRankForkClear.exists_clear_fix_axis (n + 1) q x hbf hbn
  let u : relativeRootGroup (n + 1) q := c * (b * a)
  have he : (u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v =
      (c.val : Mat (q.Extension 2) (n + 3)) *ᵥ x := by
    change (((c.val * (b.val * a.val) : (Mat (q.Extension 2) (n + 3))ˣ) :
      Mat (q.Extension 2) (n + 3)) *ᵥ v) = _
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rfl
  refine ⟨u, ?_, ?_⟩
  · simpa only [he] using hcp
  · simpa only [he] using hcn

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankZeroLastReduction
