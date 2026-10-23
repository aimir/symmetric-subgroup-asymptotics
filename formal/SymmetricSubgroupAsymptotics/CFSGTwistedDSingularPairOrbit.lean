import SymmetricSubgroupAsymptotics.CFSGTwistedDOrthogonalSecondNormalization

/-! Every independent singular pair in the actual defining-fixed
space is sent to the first positive pair by the SAME relative group.
Independence is over the literal fixed field, rather than an ambient
scalar-extension hypothesis. All characteristics are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPairOrbit
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedDRelativeFixedGroup CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexPolarForm CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexPrefixPerpendicular
open CFSGTwistedDOrthogonalSecondNormalization CFSGOrthogonalDIndexFlagVectors
open CFSGOrthogonalDGenerationForkTorus

theorem exists_singular_pair_frame (s : ℕ) (q : CFSG.PrimePower)
    (v w : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hw : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) w = w)
    (hv0 : v ≠ 0)
    (hQv : splitQuadraticForm (q.Extension 2) (s + 4) v = 0)
    (hQw : splitQuadraticForm (q.Extension 2) (s + 4) w = 0)
    (hvw : polar (q.Extension 2) v w = 0)
    (hnot : ∀ c : fixedField q, w ≠ (c : q.Extension 2) • v) :
    ∃ g : relativeRootGroup (s + 2) q,
      (g.val : Mat (q.Extension 2) (s + 4)) *ᵥ v = Pi.single (Sum.inl 0) 1 ∧
      (g.val : Mat (q.Extension 2) (s + 4)) *ᵥ w =
        Pi.single (Sum.inl (secondIndex s)) 1 := by
  obtain ⟨a, ha⟩ := CFSGTwistedDAllRankSingularOrbit.exists_normalize_all
    (s + 2) q v hv hQv hv0
  let w0 := (a.val : Mat (q.Extension 2) (s + 4)) *ᵥ w
  have hw0 := relative_preserves_fixed_vectors (s + 2) q a w hw
  have hw0Q : splitQuadraticForm (q.Extension 2) (s + 4) w0 = 0 :=
    (CFSGTwistedDAllRankHyperbolicPairs.preserves_Q (s + 2) q a w).trans hQw
  have hn : w0 (Sum.inr 0) = 0 := by
    have h := CFSGOrthogonalDAllRankQuadraticPreservation.elementary_preserves_polar
      (q.Extension 2) (s + 2)
      ⟨a.val, relativeRootGroup_le_elementary (s + 2) q a.property⟩ v w
    rw [ha, polar_positive_basis, hvw] at h
    exact h
  have ht : tailRestriction (q.Extension 2) (s + 3) w0 ≠ 0 := by
    intro hz
    have he := vector_eq_first_of_tail_zero (q.Extension 2) (s + 3) w0 hz hn
    have h0 : (0 : Fin (s + 4)) ≠ last (s + 2) := by
      intro h
      have hh := congrArg Fin.val h
      change 0 = s + 3 at hh
      omega
    let c : fixedField q := ⟨w0 (Sum.inl 0),
      CFSGTwistedDFixedVectorCoordinates.positive_fixed _ _ _ w0 hw0 0 h0⟩
    have hb := congrArg (fun x : Index (s + 4) → q.Extension 2 =>
      (↑(a.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ x) he
    change (↑(a.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ
      ((a.val : Mat (q.Extension 2) (s + 4)) *ᵥ w) =
        (↑(a.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ
          ((c : q.Extension 2) • Pi.single (Sum.inl 0) 1) at hb
    rw [← ha] at hb
    simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.inv_mul,
      Matrix.one_mulVec] at hb
    exact hnot c hb
  obtain ⟨b, hb0, hbw⟩ := exists_normalize_second s q w0 hw0 hw0Q hn ht
  refine ⟨b * a, ?_, ?_⟩
  · change ((b.val : Mat (q.Extension 2) (s + 4)) *
      (a.val : Mat (q.Extension 2) (s + 4))) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec, ha]
    exact hb0
  · change ((b.val : Mat (q.Extension 2) (s + 4)) *
      (a.val : Mat (q.Extension 2) (s + 4))) *ᵥ w = _
    rw [← Matrix.mulVec_mulVec]
    exact hbw

end SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPairOrbit
