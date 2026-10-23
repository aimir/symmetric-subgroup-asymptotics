import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairAction

/-! The actual positive terminal pair fixes its singular positive axis
and preserves the dual coordinate. These are exact natural actions in
every characteristic, independent of a fixed-group presentation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairFixedAxis
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDForkPairAction
variable (K : Type) [Field K]

theorem fix_positive_pen (s : ℕ) (t u : K) :
    (forkPair K s t u : Mat K (s + 2)) *ᵥ Pi.single (Sum.inl (pen s)) 1 =
      Pi.single (Sum.inl (pen s)) 1 := by
  rw [forkPair_mulVec]
  simp [Pi.single_apply, pen_ne_last, Ne.symm (pen_ne_last s)]

theorem preserve_negative_pen (s : ℕ) (t u : K) (v : Index (s + 2) → K) :
    ((forkPair K s t u : Mat K (s + 2)) *ᵥ v) (Sum.inr (pen s)) =
      v (Sum.inr (pen s)) := by
  rw [forkPair_mulVec]
  simp [Pi.single_apply, pen_ne_last, Ne.symm (pen_ne_last s)]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairFixedAxis
