import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeFixedGroup
import SymmetricSubgroupAsymptotics.CFSGTwistedDForkClear
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairFixedAxis

/-! A literal paired-root word clears the terminal conjugate pair and
fixes the preceding positive pole in every actual relative rank. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankForkClear
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGTwistedDRelativeElementaryGroup

theorem exists_clear_fix_axis (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 2) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2) v = v)
    (hb : v (Sum.inr (pen n)) ≠ 0) :
    ∃ u : relativeRootGroup n q,
      (u.val : Mat (q.Extension 2) (n + 2)) *ᵥ Pi.single (Sum.inl (pen n)) 1 =
        Pi.single (Sum.inl (pen n)) 1 ∧
      ((u.val : Mat (q.Extension 2) (n + 2)) *ᵥ v) (Sum.inl (last n)) = 0 ∧
      ((u.val : Mat (q.Extension 2) (n + 2)) *ᵥ v) (Sum.inr (last n)) = 0 ∧
      ((u.val : Mat (q.Extension 2) (n + 2)) *ᵥ v) (Sum.inr (pen n)) =
        v (Sum.inr (pen n)) := by
  have hσ : Function.Involutive (definingFieldAutomorphism q 2) := by
    intro a
    simpa only [definingFieldAutomorphism_apply] using
      CFSGTwistedANaturalMatrices.extension_two_pow_twice q a
  obtain ⟨t, hp, hn⟩ := CFSGTwistedDForkClear.exists_clear_last_pair (q.Extension 2) n
    (definingFieldAutomorphism q 2) hσ v hb
    (CFSGTwistedDFixedVectorCoordinates.negative_fixed (q.Extension 2) n
      (definingFieldAutomorphism q 2) v hv (pen n) (pen_ne_last n))
    (fixed_last_pair (q.Extension 2) n (definingFieldAutomorphism q 2) v hv)
  let u : relativeRootGroup n q :=
    ⟨pairedRoot n q false t, paired_mem n q false t⟩
  have he : u.val = CFSGOrthogonalDForkPairAction.forkPair (q.Extension 2) n
      t (definingFieldAutomorphism q 2 t) := rfl
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · rw [he]
    exact CFSGOrthogonalDForkPairFixedAxis.fix_positive_pen _ _ _ _
  · simpa only [he] using hp
  · simpa only [he] using hn
  · rw [he]
    exact CFSGOrthogonalDForkPairFixedAxis.preserve_negative_pen _ _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankForkClear
