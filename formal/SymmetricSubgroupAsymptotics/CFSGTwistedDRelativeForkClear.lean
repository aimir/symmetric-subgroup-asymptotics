import SymmetricSubgroupAsymptotics.CFSGTwistedDForkClear
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativePivots

/-! The explicit paired root clearing the final conjugate coordinates belongs to the literal relative-root subgroup, preserving the fixed carrier and actual quadratic form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeForkClear
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGSerreOrdinaryTwists CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedDDerivedPairedRoots CFSGTwistedDPairedRootImages
open CFSGOrthogonalDIndexBundledQuadratic
open CFSGTwistedDRelativeChainLift

theorem exists_clear_last_pair_in_relative (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hb : v (Sum.inr (pen (s + 2))) ≠ 0) :
    ∃ u : relativePreimage s q,
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (Sum.inl (last (s + 2))) = 0 ∧
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (Sum.inr (last (s + 2))) = 0 ∧
      vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2)
          ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) =
        (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v ∧
      splitQuadraticForm (q.Extension 2) (s + 4)
          ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) =
        splitQuadraticForm (q.Extension 2) (s + 4) v := by
  have hσ : Function.Involutive (definingFieldAutomorphism q 2) := by
    intro a
    simpa only [definingFieldAutomorphism_apply] using
      CFSGTwistedANaturalMatrices.extension_two_pow_twice q a
  obtain ⟨t, hp, hn⟩ := CFSGTwistedDForkClear.exists_clear_last_pair (q.Extension 2) (s + 2)
    (definingFieldAutomorphism q 2) hσ v hb
    (CFSGTwistedDFixedVectorCoordinates.negative_fixed (q.Extension 2) (s + 2)
      (definingFieldAutomorphism q 2) v hv (pen (s + 2)) (pen_ne_last (s + 2)))
    (fixed_last_pair (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v hv)
  let u : relativePreimage s q :=
    ⟨pairedNaturalRoot s q false t, CFSGTwistedDRelativeChainLift.paired_mem s q false t⟩
  have he : u.val.val = CFSGOrthogonalDForkPairAction.forkPair (q.Extension 2) (s + 2)
      t (definingFieldAutomorphism q 2 t) := by
    change rootTransvection (q.Extension 2) (s + 4) false (pen (s + 2)) t *
        rootTransvection (q.Extension 2) (s + 4) false (last (s + 2)) (t^q.order) = _
    rw [definingFieldAutomorphism_apply] <;> rfl
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · simpa only [he] using hp
  · simpa only [he] using hn
  · exact CFSGTwistedDRelativePivots.preserves_fixed s q u v hv
  · exact elementary_preserves_bundledQ (q.Extension 2) s u.val v

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeForkClear
