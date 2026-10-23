import SymmetricSubgroupAsymptotics.CFSGTwistedDZeroLastNormalization
import SymmetricSubgroupAsymptotics.CFSGTwistedDZeroLastReduction

/-! Actual singular-vector normalization above the original Derived
action image: clear the anisotropic final pair, then use the retained
smaller split-D block. No full fixed-group generation is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSingularVectorNormalization
open CFSGOrthogonalDSerreMatrices CFSGTwistedDNaturalQuadraticTwist
open CFSGSerreOrdinaryTwists CFSGTwistedDDerivedPairedRoots
open CFSGOrthogonalDIndexBundledQuadratic

theorem exists_normalize_singular (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (s + 4) v = 0) (hv0 : v ≠ 0) :
    ∃ u : naturalDerivedPreimage s q,
      (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v = Pi.single (Sum.inl 0) 1 := by
  obtain ⟨a, hap, han⟩ :=
    CFSGTwistedDZeroLastReduction.exists_clear_last_pair s q v hv hQ hv0
  let w := (a.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v
  have hw : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) w = w :=
    CFSGTwistedDFixedVectorAction.derived_preserves_fixed_vectors s q a v hv
  have hwQ : splitQuadraticForm (q.Extension 2) (s + 4) w = 0 :=
    (elementary_preserves_bundledQ (q.Extension 2) s a.val v).trans hQ
  have hw0 : w ≠ 0 := by
    intro hz
    apply hv0
    have he := congrArg (fun x : Index (s + 4) → q.Extension 2 =>
      (↑(a.val.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ x) hz
    change (↑(a.val.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ
      ((a.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) =
        (↑(a.val.val⁻¹) : Mat (q.Extension 2) (s + 4)) *ᵥ 0 at he
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_zero] using he
  obtain ⟨b, hb⟩ := CFSGTwistedDZeroLastNormalization.exists_normalize
    s q w hw hap han hwQ hw0
  refine ⟨b * a, ?_⟩
  change ((b.val.val : Mat (q.Extension 2) (s + 4)) *
    (a.val.val : Mat (q.Extension 2) (s + 4))) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]
  exact hb

end SymmetricSubgroupAsymptotics.CFSGTwistedDSingularVectorNormalization
