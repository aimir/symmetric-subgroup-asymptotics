import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCompanionLastClear
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCompanionBlock
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeSingularVectorNormalization

/-! Explicit hyperbolic-pair normalization in the literal relative-root
subgroup. Both original vectors, the defining involution, and the actual
quadratic and polar forms remain on their original natural carrier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeHyperbolicPairNormalization
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeChainLift
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexPrefixPerpendicular

theorem exists_normalize_companion (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (s + 4) v = 0)
    (hy : v (Sum.inr 0) = 1) :
    ∃ c : relativePreimage s q,
      (c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ Pi.single (Sum.inl 0) 1 =
        Pi.single (Sum.inl 0) 1 ∧
      (c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v = Pi.single (Sum.inr 0) 1 := by
  obtain ⟨a, haxis, hp, hn, hay⟩ :=
    CFSGTwistedDRelativeCompanionLastClear.exists_clear_fix_first s q v hv hy
  let w := (a.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v
  have hw := CFSGTwistedDRelativePivots.preserves_fixed s q a v hv
  have hwQ : splitQuadraticForm (q.Extension 2) (s + 4) w = 0 :=
    (elementary_preserves_bundledQ (q.Extension 2) s a.val v).trans hQ
  obtain ⟨b, hbaxis, hb⟩ :=
    CFSGTwistedDRelativeCompanionBlock.exists_normalize_fix_first s q w hw hp hn hwQ hay
  refine ⟨b * a, ?_, ?_⟩
  · change ((b.val.val : Mat (q.Extension 2) (s + 4)) *
      (a.val.val : Mat (q.Extension 2) (s + 4))) *ᵥ Pi.single (Sum.inl 0) 1 = _
    rw [← Matrix.mulVec_mulVec, haxis, hbaxis]
  · change ((b.val.val : Mat (q.Extension 2) (s + 4)) *
      (a.val.val : Mat (q.Extension 2) (s + 4))) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec]
    exact hb

theorem exists_normalize_pair (s : ℕ) (q : CFSG.PrimePower)
    (u v : Index (s + 4) → q.Extension 2)
    (hu : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) u = u)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hQu : splitQuadraticForm (q.Extension 2) (s + 4) u = 0)
    (hQv : splitQuadraticForm (q.Extension 2) (s + 4) v = 0)
    (hu0 : u ≠ 0) (hB : polar (q.Extension 2) u v = 1) :
    ∃ c : relativePreimage s q,
      (c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ u = Pi.single (Sum.inl 0) 1 ∧
      (c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v = Pi.single (Sum.inr 0) 1 := by
  obtain ⟨a, ha⟩ :=
    CFSGTwistedDRelativeSingularVectorNormalization.exists_normalize_singular s q u hu hQu hu0
  let w := (a.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v
  have hw := CFSGTwistedDRelativePivots.preserves_fixed s q a v hv
  have hwQ : splitQuadraticForm (q.Extension 2) (s + 4) w = 0 :=
    (elementary_preserves_bundledQ (q.Extension 2) s a.val v).trans hQv
  have hy : w (Sum.inr 0) = 1 := by
    have h := elementary_preserves_polar (q.Extension 2) s a.val u v
    rw [ha, polar_positive_basis, hB] at h
    exact h
  obtain ⟨b, hbaxis, hb⟩ := exists_normalize_companion s q w hw hwQ hy
  refine ⟨b * a, ?_, ?_⟩
  · change ((b.val.val : Mat (q.Extension 2) (s + 4)) *
      (a.val.val : Mat (q.Extension 2) (s + 4))) *ᵥ u = _
    rw [← Matrix.mulVec_mulVec, ha, hbaxis]
  · change ((b.val.val : Mat (q.Extension 2) (s + 4)) *
      (a.val.val : Mat (q.Extension 2) (s + 4))) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec]
    exact hb

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeHyperbolicPairNormalization
