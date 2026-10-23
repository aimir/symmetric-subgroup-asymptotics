import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeNormScaling
import SymmetricSubgroupAsymptotics.CFSGTwistedDRankTwoWeyl
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllRankQuadraticPreservation
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDForkClear

/-! Genuine rank-two singular-vector normalization. The witnesses are
paired relative roots, their Weyl word, and the actual finite-field norm
torus. No PSL2/SO3 or fixed-group recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRankTwoSingularOrbit
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeNormScaling
open CFSGTwistedDRelativeFixedGroup CFSGTwistedDNaturalQuadraticTwist
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexQuadraticForm CFSGTwistedDFixedVectorCoordinates

theorem splitQ_two (K : Type) [Field K] (v : Index 2 → K) :
    splitQ K v = v (Sum.inl 0) * v (Sum.inr 0) +
      v (Sum.inl 1) * v (Sum.inr 1) := by
  change (∑ i : Fin 2, v (Sum.inl i) * v (Sum.inr i)) = _
  rw [Fin.sum_univ_two]

theorem exists_normalize_singular (q : CFSG.PrimePower)
    (v : Index 2 → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) 0 (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQ (q.Extension 2) v = 0) (hv0 : v ≠ 0) :
    ∃ u : relativeRootGroup 0 q,
      (u.val : Mat (q.Extension 2) 2) *ᵥ v = Pi.single (Sum.inl 0) 1 := by
  let σ := definingFieldAutomorphism q 2
  have hσ : Function.Involutive σ := by
    intro a
    simpa only [σ, definingFieldAutomorphism_apply] using
      CFSGTwistedANaturalMatrices.extension_two_pow_twice q a
  have hpair : v (Sum.inr 1) = σ (v (Sum.inl 1)) :=
    fixed_last_pair (q.Extension 2) 0 σ v hv
  have hxσ : σ (v (Sum.inl 0)) = v (Sum.inl 0) :=
    positive_fixed (q.Extension 2) 0 σ v hv 0 (pen_ne_last 0)
  have hyσ : σ (v (Sum.inr 0)) = v (Sum.inr 0) :=
    negative_fixed (q.Extension 2) 0 σ v hv 0 (pen_ne_last 0)
  by_cases hy : v (Sum.inr 0) = 0
  · have hz : v (Sum.inl 1) = 0 := by
      rw [splitQ_two, hy, mul_zero, zero_add, hpair] at hQ
      rcases mul_eq_zero.mp hQ with hz | hz
      · exact hz
      · exact σ.injective (hz.trans (map_zero σ).symm)
    have hn : v (Sum.inr 1) = 0 := by rw [hpair, hz, map_zero]
    have he : v = Pi.single (Sum.inl 0) (v (Sum.inl 0)) := by
      funext x
      cases x with
      | inl i => fin_cases i <;> simp [Pi.single_apply, hz]
      | inr i => fin_cases i <;> simp [Pi.single_apply, hy, hn]
    let x : fixedField q := ⟨v (Sum.inl 0), hxσ⟩
    have hx : x ≠ 0 := by
      intro h
      have hx0 : v (Sum.inl 0) = 0 := congrArg (fun z : fixedField q => (z : q.Extension 2)) h
      apply hv0
      rw [he, hx0]
      simp
    obtain ⟨u, hu⟩ := exists_scale_positive_axis 0 q (Units.mk0 x hx)
    refine ⟨u, ?_⟩
    rw [he]
    exact hu
  · obtain ⟨t, hp, hn⟩ := CFSGTwistedDForkClear.exists_clear_last_pair
      (q.Extension 2) 0 σ hσ v hy hyσ hpair
    let a : relativeRootGroup 0 q := ⟨pairedRoot 0 q false t, paired_mem 0 q false t⟩
    let w := (a.val : Mat (q.Extension 2) 2) *ᵥ v
    have ha : a.val = CFSGOrthogonalDForkPairAction.forkPair (q.Extension 2) 0 t (σ t) := rfl
    have hwp : w (Sum.inl 1) = 0 := by simpa only [ha] using hp
    have hwn : w (Sum.inr 1) = 0 := by simpa only [ha] using hn
    have hwy : w (Sum.inr 0) = v (Sum.inr 0) := by
      change ((a.val : Mat (q.Extension 2) 2) *ᵥ v) (Sum.inr 0) = _
      rw [ha, CFSGOrthogonalDForkPairAction.forkPair_mulVec]
      simp [pen, last, Pi.single_apply]
    have hwQ : splitQ (q.Extension 2) w = 0 := by
      exact (CFSGOrthogonalDAllRankQuadraticPreservation.elementary_preserves
        (q.Extension 2) 0 ⟨a.val, relativeRootGroup_le_elementary 0 q a.property⟩ v).trans hQ
    have hwx : w (Sum.inl 0) = 0 := by
      rw [splitQ_two, hwp, zero_mul, add_zero, hwy] at hwQ
      exact (mul_eq_zero.mp hwQ).resolve_right hy
    have he : w = Pi.single (Sum.inr 0) (v (Sum.inr 0)) := by
      funext x
      cases x with
      | inl i => fin_cases i <;> simp [Pi.single_apply, hwx, hwp]
      | inr i => fin_cases i <;> simp [Pi.single_apply, hwy, hwn]
    let y : fixedField q := ⟨v (Sum.inr 0), hyσ⟩
    have hyF : y ≠ 0 := fun h => hy
      (congrArg (fun z : fixedField q => (z : q.Extension 2)) h)
    obtain ⟨c, hc⟩ := exists_scale_positive_axis 0 q
      (Units.mk0 (-y) (neg_ne_zero.mpr hyF))
    let b := CFSGTwistedDRankTwoWeyl.weyl q
    refine ⟨c * (b * a), ?_⟩
    change ((c.val : Mat (q.Extension 2) 2) *
      ((b.val : Mat (q.Extension 2) 2) * (a.val : Mat (q.Extension 2) 2))) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (c.val : Mat (q.Extension 2) 2) *ᵥ ((b.val : Mat (q.Extension 2) 2) *ᵥ w) = _
    rw [he, CFSGTwistedDRankTwoWeyl.negative_axis_parameter]
    exact hc

end SymmetricSubgroupAsymptotics.CFSGTwistedDRankTwoSingularOrbit
