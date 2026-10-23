import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankCompanionLastClear
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankCompanionBlock
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankSingularOrbit
import SymmetricSubgroupAsymptotics.CFSGTwistedDRankTwoCompanion

/-! Exact all-rank hyperbolic-pair normalization by actual relative-root
words, including the genuine rank-two base. The defining fixed-vector
carrier and quadratic form remain literal in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankHyperbolicPairs
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexPrefixPerpendicular

theorem preserves_Q (n : ℕ) (q : CFSG.PrimePower) (u : relativeRootGroup n q)
    (v : Index (n + 2) → q.Extension 2) :
    splitQuadraticForm (q.Extension 2) (n + 2) ((u.val : Mat (q.Extension 2) (n + 2)) *ᵥ v) =
      splitQuadraticForm (q.Extension 2) (n + 2) v := by
  rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
  exact CFSGOrthogonalDAllRankQuadraticPreservation.elementary_preserves
    (q.Extension 2) n ⟨u.val, relativeRootGroup_le_elementary n q u.property⟩ v

theorem exists_normalize_companion (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (n + 3) v = 0)
    (hy : v (Sum.inr 0) = 1) :
    ∃ c : relativeRootGroup (n + 1) q,
      (c.val : Mat (q.Extension 2) (n + 3)) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
      (c.val : Mat (q.Extension 2) (n + 3)) *ᵥ v = Pi.single (Sum.inr 0) 1 := by
  obtain ⟨a, haxis, hp, hn, hay⟩ :=
    CFSGTwistedDAllRankCompanionLastClear.exists_clear_fix_first n q v hv hy
  let w := (a.val : Mat (q.Extension 2) (n + 3)) *ᵥ v
  have hw := CFSGTwistedDRelativeFixedGroup.relative_preserves_fixed_vectors (n + 1) q a v hv
  have hwQ : splitQuadraticForm (q.Extension 2) (n + 3) w = 0 :=
    (preserves_Q (n + 1) q a v).trans hQ
  obtain ⟨b, hbaxis, hb⟩ :=
    CFSGTwistedDAllRankCompanionBlock.exists_normalize_fix_first n q w hw hp hn hwQ hay
  refine ⟨b * a, ?_, ?_⟩
  · change ((b.val : Mat (q.Extension 2) (n + 3)) *
      (a.val : Mat (q.Extension 2) (n + 3))) *ᵥ Pi.single (Sum.inl 0) 1 = _
    rw [← Matrix.mulVec_mulVec, haxis, hbaxis]
  · change ((b.val : Mat (q.Extension 2) (n + 3)) * (a.val : Mat (q.Extension 2) (n + 3))) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec]
    exact hb

theorem exists_normalize_companion_all (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 2) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (n + 2) v = 0) (hy : v (Sum.inr 0) = 1) :
    ∃ c : relativeRootGroup n q,
      (c.val : Mat (q.Extension 2) (n + 2)) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
      (c.val : Mat (q.Extension 2) (n + 2)) *ᵥ v = Pi.single (Sum.inr 0) 1 := by
  cases n with
  | zero =>
    exact CFSGTwistedDRankTwoCompanion.exists_normalize_companion q v hv
      ((splitQuadraticForm_apply (q.Extension 2) 2 v).symm.trans hQ) hy
  | succ n => exact exists_normalize_companion n q v hv hQ hy

theorem exists_normalize_pair (n : ℕ) (q : CFSG.PrimePower)
    (u v : Index (n + 2) → q.Extension 2)
    (hu : vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2) u = u)
    (hv : vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2) v = v)
    (hQu : splitQuadraticForm (q.Extension 2) (n + 2) u = 0)
    (hQv : splitQuadraticForm (q.Extension 2) (n + 2) v = 0)
    (hu0 : u ≠ 0) (hB : polar (q.Extension 2) u v = 1) :
    ∃ c : relativeRootGroup n q,
      (c.val : Mat (q.Extension 2) (n + 2)) *ᵥ u = Pi.single (Sum.inl 0) 1 ∧
      (c.val : Mat (q.Extension 2) (n + 2)) *ᵥ v = Pi.single (Sum.inr 0) 1 := by
  obtain ⟨a, ha⟩ := CFSGTwistedDAllRankSingularOrbit.exists_normalize_all n q u hu hQu hu0
  let w := (a.val : Mat (q.Extension 2) (n + 2)) *ᵥ v
  have hw := CFSGTwistedDRelativeFixedGroup.relative_preserves_fixed_vectors n q a v hv
  have hwQ : splitQuadraticForm (q.Extension 2) (n + 2) w = 0 :=
    (preserves_Q n q a v).trans hQv
  have hy : w (Sum.inr 0) = 1 := by
    have h := CFSGOrthogonalDAllRankQuadraticPreservation.elementary_preserves_polar
      (q.Extension 2) n ⟨a.val, relativeRootGroup_le_elementary n q a.property⟩ u v
    rw [ha, polar_positive_basis, hB] at h
    exact h
  obtain ⟨b, hbaxis, hb⟩ := exists_normalize_companion_all n q w hw hwQ hy
  refine ⟨b * a, ?_, ?_⟩
  · change ((b.val : Mat (q.Extension 2) (n + 2)) * (a.val : Mat (q.Extension 2) (n + 2))) *ᵥ u = _
    rw [← Matrix.mulVec_mulVec, ha, hbaxis]
  · change ((b.val : Mat (q.Extension 2) (n + 2)) * (a.val : Mat (q.Extension 2) (n + 2))) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec]
    exact hb

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankHyperbolicPairs
