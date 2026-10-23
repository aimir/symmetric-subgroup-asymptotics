import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankAxisTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankForkClear
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPivots
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllRankQuadraticPreservation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixPerpendicular

/-! An actual relative word fixing the first positive pole clears a
companion's final pair, uniformly in relative ranks at least three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankCompanionLastClear
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDAllRankAxisTransport
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGOrthogonalDIndexPolarForm CFSGOrthogonalDIndexPrefixPerpendicular

theorem exists_clear_fix_first (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hy : v (Sum.inr 0) = 1) :
    ∃ c : relativeRootGroup (n + 1) q,
      (c.val : Mat (q.Extension 2) (n + 3)) *ᵥ Pi.single (Sum.inl 0) 1 =
        Pi.single (Sum.inl 0) 1 ∧
      ((c.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
        (Sum.inl (last (n + 1))) = 0 ∧
      ((c.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
        (Sum.inr (last (n + 1))) = 0 ∧
      ((c.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) (Sum.inr 0) = 1 := by
  obtain ⟨a, ha, hlast⟩ := exists_axis_to_pen n q
  let w := (a.val : Mat (q.Extension 2) (n + 3)) *ᵥ v
  have hw := CFSGTwistedDAllRankPivots.preserves_fixed n q a v hv
  have hp : w (Sum.inr (pen (n + 1))) = 1 := by
    have h := CFSGOrthogonalDAllRankQuadraticPreservation.elementary_preserves_polar
      (q.Extension 2) (n + 1) ⟨a.val, relativeRootGroup_le_elementary (n + 1) q a.property⟩
      (Pi.single (Sum.inl 0) 1) v
    rw [ha, polar_positive_basis, polar_positive_basis, hy] at h
    exact h
  obtain ⟨b, hb, hbp, hbn, _⟩ :=
    CFSGTwistedDAllRankForkClear.exists_clear_fix_axis (n + 1) q w hw
      (hp.trans_ne one_ne_zero)
  have hai : (↑(a.val⁻¹) : Mat (q.Extension 2) (n + 3)) *ᵥ
      Pi.single (Sum.inl (pen (n + 1))) 1 = Pi.single (Sum.inl 0) 1 := by
    rw [← ha, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hlastInv (x : Index (n + 3) → q.Extension 2) :
      ((↑(a.val⁻¹) : Mat (q.Extension 2) (n + 3)) *ᵥ x)
          (Sum.inl (last (n + 1))) = x (Sum.inl (last (n + 1))) ∧
      ((↑(a.val⁻¹) : Mat (q.Extension 2) (n + 3)) *ᵥ x)
          (Sum.inr (last (n + 1))) = x (Sum.inr (last (n + 1))) := by
    have h := hlast ((↑(a.val⁻¹) : Mat (q.Extension 2) (n + 3)) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    exact ⟨h.1.symm, h.2.symm⟩
  let c : relativeRootGroup (n + 1) q := a⁻¹ * (b * a)
  have hc (x : Index (n + 3) → q.Extension 2) :
      (c.val : Mat (q.Extension 2) (n + 3)) *ᵥ x =
        (↑(a.val⁻¹) : Mat (q.Extension 2) (n + 3)) *ᵥ
          ((b.val : Mat (q.Extension 2) (n + 3)) *ᵥ
            ((a.val : Mat (q.Extension 2) (n + 3)) *ᵥ x)) := by
    change ((↑(a.val⁻¹) : Mat (q.Extension 2) (n + 3)) *
      ((b.val : Mat (q.Extension 2) (n + 3)) *
        (a.val : Mat (q.Extension 2) (n + 3)))) *ᵥ x = _
    simp only [← Matrix.mulVec_mulVec]
  have haxis : (c.val : Mat (q.Extension 2) (n + 3)) *ᵥ
      Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 := by
    rw [hc, ha, hb, hai]
  refine ⟨c, haxis, ?_, ?_, ?_⟩
  · rw [hc]
    exact (hlastInv ((b.val : Mat (q.Extension 2) (n + 3)) *ᵥ w)).1.trans hbp
  · rw [hc]
    exact (hlastInv ((b.val : Mat (q.Extension 2) (n + 3)) *ᵥ w)).2.trans hbn
  · have h := CFSGOrthogonalDAllRankQuadraticPreservation.elementary_preserves_polar
      (q.Extension 2) (n + 1) ⟨c.val, relativeRootGroup_le_elementary (n + 1) q c.property⟩
      (Pi.single (Sum.inl 0) 1) v
    rw [haxis, polar_positive_basis, polar_positive_basis, hy] at h
    exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankCompanionLastClear
