import SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicColumn

/-! A literal B isometry fixing the middle vector has an actual paired
block and the unchanged middle coordinate. No choice of quotient or
complement is involved. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBFixedMiddleBlock
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIndexForm
open CFSGOrthogonalBSpecialFormGroup CFSGOrthogonalBParabolicColumn
variable (K : Type) [Field K]

theorem fixed_middle_block (n : ℕ) (g : formUnits K n)
    (hcol : (g.val : Mat K n) *ᵥ Pi.single (middle n) 1 = Pi.single (middle n) 1) :
    (g.val : Mat K n) = Matrix.fromBlocks (g.val : Mat K n).toBlocks₁₁ 0 0 1 := by
  have hrow (j : Fin n ⊕ Fin n) : (g.val : Mat K n) (middle n) (Sum.inl j) = 0 := by
    have hh := pairing_invariant K n g (Pi.single (Sum.inl j) 1) (Pi.single (middle n) 1)
    rw [hcol, pairing_middle, pairing_middle] at hh
    simpa [Matrix.mulVec_single_one, Matrix.col, middle, Pi.single_apply] using hh
  ext x y
  rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩
  · rfl
  · have hh := congrFun hcol (Sum.inl x)
    simpa [Matrix.mulVec_single_one, Matrix.col, Matrix.fromBlocks, middle, Pi.single_apply] using hh
  · exact hrow y
  · have hh := congrFun hcol (middle n)
    simpa [Matrix.mulVec_single_one, Matrix.col, Matrix.fromBlocks, middle, Pi.single_apply] using hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBFixedMiddleBlock
