import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeNegativeSupport
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativePivots
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeForkClear

/-! Every nonzero singular fixed vector has its final conjugate pair cleared by an explicit product in the literal relative-root subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeZeroLastReduction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGSerreOrdinaryTwists CFSGTwistedDNaturalQuadraticTwist
open CFSGOrthogonalDIndexBundledQuadratic CFSGTwistedDDerivedPairedRoots
open CFSGTwistedDRelativeChainLift

theorem exists_clear_last_pair (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (s + 4) v = 0) (hv0 : v ≠ 0) :
    ∃ u : relativePreimage s q,
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inl (last (s + 2))) = 0 ∧
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inr (last (s + 2))) = 0 := by
  obtain ⟨a, ha⟩ := CFSGTwistedDRelativeNegativeSupport.exists_negative_support s q v hv hQ hv0
  let w := (a.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v
  have hw : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) w = w :=
    CFSGTwistedDRelativePivots.preserves_fixed s q a v hv
  obtain ⟨b, hb, hbf⟩ := CFSGTwistedDRelativePivots.exists_negative_pivot s q w hw ha
  let x := (b.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ w
  have hbn : x (Sum.inr (pen (s + 2))) ≠ 0 := by
    change ((b.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ w)
      (Sum.inr (pen (s + 2))) ≠ 0
    rw [hb]
    exact one_ne_zero
  obtain ⟨c, hcp, hcn, _, _⟩ :=
    CFSGTwistedDRelativeForkClear.exists_clear_last_pair_in_relative s q x hbf hbn
  let u : relativePreimage s q := c * (b * a)
  have he : (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v =
      (c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ x := by
    change (((c.val.val * (b.val.val * a.val.val) : (Mat (q.Extension 2) (s + 4))ˣ) :
      Mat (q.Extension 2) (s + 4)) *ᵥ v) = _
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rfl
  refine ⟨u, ?_, ?_⟩
  · simpa only [he] using hcp
  · simpa only [he] using hcn

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeZeroLastReduction
