import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeForkClear
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairFixedAxis

/-! A literal relative paired-root word clears the anisotropic coordinates while fixing the preceding positive axis and preserving its dual coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeForkClearAxis
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGTwistedDDerivedPairedRoots CFSGTwistedDPairedRootImages
open CFSGTwistedDRelativeChainLift

theorem exists_clear_fix_axis (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hb : v (Sum.inr (pen (s + 2))) ≠ 0) :
    ∃ u : relativePreimage s q,
      (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ Pi.single (Sum.inl (pen (s + 2))) 1 =
        Pi.single (Sum.inl (pen (s + 2))) 1 ∧
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (Sum.inl (last (s + 2))) = 0 ∧
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (Sum.inr (last (s + 2))) = 0 ∧
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (Sum.inr (pen (s + 2))) =
        v (Sum.inr (pen (s + 2))) := by
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
      rootTransvection (q.Extension 2) (s + 4) false (last (s + 2)) (t ^ q.order) = _
    rw [definingFieldAutomorphism_apply] <;> rfl
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · rw [he]
    exact CFSGOrthogonalDForkPairFixedAxis.fix_positive_pen _ _ _ _
  · simpa only [he] using hp
  · simpa only [he] using hn
  · rw [he]
    exact CFSGOrthogonalDForkPairFixedAxis.preserve_negative_pen _ _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeForkClearAxis
