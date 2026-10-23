import SymmetricSubgroupAsymptotics.CFSGTwistedDRankTwoSingularOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairFixedAxis

/-! A literal paired positive root fixes the first positive pole and
normalizes every rank-two singular companion with dual coordinate one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRankTwoCompanion
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeFixedGroup
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGTwistedDFixedVectorCoordinates CFSGOrthogonalDIndexQuadraticForm
open CFSGTwistedDRankTwoSingularOrbit

theorem exists_normalize_companion (q : CFSG.PrimePower)
    (v : Index 2 → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) 0 (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQ (q.Extension 2) v = 0) (hy : v (Sum.inr 0) = 1) :
    ∃ u : relativeRootGroup 0 q,
      (u.val : Mat (q.Extension 2) 2) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
      (u.val : Mat (q.Extension 2) 2) *ᵥ v = Pi.single (Sum.inr 0) 1 := by
  let σ := definingFieldAutomorphism q 2
  have hσ : Function.Involutive σ := by
    intro a
    simpa only [σ, definingFieldAutomorphism_apply] using
      CFSGTwistedANaturalMatrices.extension_two_pow_twice q a
  have hyσ : σ (v (Sum.inr 0)) = v (Sum.inr 0) :=
    negative_fixed (q.Extension 2) 0 σ v hv 0 (pen_ne_last 0)
  obtain ⟨t, hp, hn⟩ := CFSGTwistedDForkClear.exists_clear_last_pair
    (q.Extension 2) 0 σ hσ v (hy.trans_ne one_ne_zero) hyσ
      (fixed_last_pair (q.Extension 2) 0 σ v hv)
  let u : relativeRootGroup 0 q := ⟨pairedRoot 0 q false t, paired_mem 0 q false t⟩
  have he : u.val = CFSGOrthogonalDForkPairAction.forkPair (q.Extension 2) 0 t (σ t) := rfl
  have haxis : (u.val : Mat (q.Extension 2) 2) *ᵥ Pi.single (Sum.inl 0) 1 =
      Pi.single (Sum.inl 0) 1 := by
    rw [he]
    exact CFSGOrthogonalDForkPairFixedAxis.fix_positive_pen _ _ _ _
  let w := (u.val : Mat (q.Extension 2) 2) *ᵥ v
  have hwp : w (Sum.inl 1) = 0 := by simpa only [he] using hp
  have hwn : w (Sum.inr 1) = 0 := by simpa only [he] using hn
  have hwy : w (Sum.inr 0) = 1 := by
    change ((u.val : Mat (q.Extension 2) 2) *ᵥ v) (Sum.inr 0) = _
    rw [he]
    change ((CFSGOrthogonalDForkPairAction.forkPair (q.Extension 2) 0 t (σ t) :
      Mat (q.Extension 2) 2) *ᵥ v) (Sum.inr (pen 0)) = 1
    rw [CFSGOrthogonalDForkPairFixedAxis.preserve_negative_pen]
    exact hy
  have hwQ : splitQ (q.Extension 2) w = 0 :=
    (CFSGOrthogonalDAllRankQuadraticPreservation.elementary_preserves
      (q.Extension 2) 0 ⟨u.val, relativeRootGroup_le_elementary 0 q u.property⟩ v).trans hQ
  have hwx : w (Sum.inl 0) = 0 := by
    rw [splitQ_two, hwp, zero_mul, add_zero, hwy, mul_one] at hwQ
    exact hwQ
  refine ⟨u, haxis, ?_⟩
  change w = _
  funext x
  cases x with
  | inl i => fin_cases i <;> simp [hwx, hwp]
  | inr i => fin_cases i <;> simp [hwy, hwn]

end SymmetricSubgroupAsymptotics.CFSGTwistedDRankTwoCompanion
