import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeAxisTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeForkClearAxis
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixPerpendicular

/-! A conjugate of the literal paired-root clearing word fixes the
first positive pole, clears a normalized companion's final conjugate
pair, and retains its dual first coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCompanionLastClear
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeChainLift CFSGTwistedDRelativeAxisTransport
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGOrthogonalDIndexPolarForm CFSGOrthogonalDIndexPrefixPerpendicular

theorem exists_clear_fix_first (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hy : v (Sum.inr 0) = 1) :
    ∃ c : relativePreimage s q,
      (c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ Pi.single (Sum.inl 0) 1 =
        Pi.single (Sum.inl 0) 1 ∧
      ((c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inl (last (s + 2))) = 0 ∧
      ((c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inr (last (s + 2))) = 0 ∧
      ((c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (Sum.inr 0) = 1 := by
  obtain ⟨a, ha, hlast⟩ := exists_axis_to_pen s q
  let w := (a.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v
  have hw := CFSGTwistedDRelativePivots.preserves_fixed s q a v hv
  have hp : w (Sum.inr (pen (s + 2))) = 1 := by
    have h := elementary_preserves_polar (q.Extension 2) s a.val
      (Pi.single (Sum.inl 0) 1) v
    rw [ha, polar_positive_basis, polar_positive_basis, hy] at h
    exact h
  obtain ⟨b, hb, hbp, hbn, _⟩ :=
    CFSGTwistedDRelativeForkClearAxis.exists_clear_fix_axis s q w hw
      (hp.trans_ne one_ne_zero)
  have hai : (↑(a.val.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ
      Pi.single (Sum.inl (pen (s + 2))) 1 = Pi.single (Sum.inl 0) 1 := by
    rw [← ha, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hlastInv (x : Index (s + 4) → q.Extension 2) :
      ((↑(a.val.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ x)
          (Sum.inl (last (s + 2))) = x (Sum.inl (last (s + 2))) ∧
      ((↑(a.val.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ x)
          (Sum.inr (last (s + 2))) = x (Sum.inr (last (s + 2))) := by
    have h := hlast ((↑(a.val.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    exact ⟨h.1.symm, h.2.symm⟩
  let c : relativePreimage s q := a⁻¹ * (b * a)
  have hc (x : Index (s + 4) → q.Extension 2) :
      (c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ x =
        (↑(a.val.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ
          ((b.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ
            ((a.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ x)) := by
    change ((↑(a.val.val⁻¹) : Mat (q.Extension 2) (s + 4)) *
      ((b.val.val : Mat (q.Extension 2) (s + 4)) *
        (a.val.val : Mat (q.Extension 2) (s + 4)))) *ᵥ x = _
    simp only [← Matrix.mulVec_mulVec]
  have haxis : (c.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ
      Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 := by
    rw [hc, ha, hb, hai]
  refine ⟨c, haxis, ?_, ?_, ?_⟩
  · rw [hc]
    exact (hlastInv ((b.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ w)).1.trans hbp
  · rw [hc]
    exact (hlastInv ((b.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ w)).2.trans hbn
  · have h := elementary_preserves_polar (q.Extension 2) s c.val
      (Pi.single (Sum.inl 0) 1) v
    rw [haxis, polar_positive_basis, polar_positive_basis, hy] at h
    exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeCompanionLastClear
