import SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicRightClear
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicMiddle
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicFactor
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBLastDiagonal

/-! The actual positive-space stabilizer is covered on one side by
last-pair diagonal parameters and SAME original elementary words.
Right-clearing avoids any assumption that the elementary group is normal. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicCoset
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIndexForm
open CFSGOrthogonalBSpecialFormGroup CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBGeneralLinearLift CFSGOrthogonalBLastDiagonal
variable (K : Type) [Field K]

theorem parabolic_one_sided_factor (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (g : specialFormUnits K (s + 1))
    (hP : (positiveSubspace K (s + 1)).map
      (Matrix.mulVecLin (g.val : Mat K (s + 1))) = positiveSubspace K (s + 1)) :
    ∃ a : Kˣ, ∃ e : elementaryRootGroup K (s + 1), g.val = lastDiagonalHom K s a * e.val := by
  let f : formUnits K (s + 1) := ⟨g.val, g.property.1⟩
  obtain ⟨b, c, hc, hbfix, hbcol⟩ :=
    CFSGOrthogonalBParabolicRightClear.exists_right_clear_middle K h2 s f hP
  let gb : specialFormUnits K (s + 1) :=
    ⟨g.val * b.val, (specialFormUnits K (s + 1)).mul_mem g.property
      (elementary_le_specialFormUnits K p h2 (s + 1) b.property)⟩
  have hnp : ∀ i j, (gb.val : Mat K (s + 1)) (neg (s + 1) i) (pos (s + 1) j) = 0 := by
    intro i j
    let v : Index (s + 1) → K := Pi.single (pos (s + 1) j) 1
    have hv : v ∈ positiveSubspace K (s + 1) := by
      apply (mem_positiveSubspace K (s + 1) v).mpr
      exact ⟨fun i => by simp [v, pos, neg], by simp [v, pos, middle]⟩
    have hg : (g.val : Mat K (s + 1)) *ᵥ v ∈ positiveSubspace K (s + 1) := by
      rw [← hP]
      exact ⟨v, hv, rfl⟩
    have hz := ((mem_positiveSubspace K (s + 1) _).mp hg).1 i
    have hh : (gb.val : Mat K (s + 1)) *ᵥ v = (g.val : Mat K (s + 1)) *ᵥ v := by
      change ((g.val : Mat K (s + 1)) * (b.val : Mat K (s + 1))) *ᵥ v = _
      rw [← Matrix.mulVec_mulVec, hbfix v hv]
    have he := congrFun hh (neg (s + 1) i)
    rw [hz] at he
    simpa [v, Matrix.mulVec_single_one, Matrix.col] using he
  have hcol : (gb.val : Mat K (s + 1)) *ᵥ Pi.single (middle (s + 1)) 1 =
      c • Pi.single (middle (s + 1)) 1 := hbcol
  have hc1 := CFSGOrthogonalBParabolicMiddle.middle_scalar_eq_one K h2 (s + 1) gb c hcol hnp
  rw [hc1, one_smul] at hcol
  obtain ⟨A, e₁, he₁⟩ := CFSGOrthogonalBParabolicFactor.fixed_middle_factor K h2 s gb hcol hnp
  obtain ⟨e₂, he₂⟩ := generalLinearLift_factor K s A
  refine ⟨Matrix.GeneralLinearGroup.det A, e₂ * e₁ * b⁻¹, ?_⟩
  have hh : g.val * b.val = lastDiagonalHom K s (Matrix.GeneralLinearGroup.det A) *
      (e₂.val * e₁.val) := by
    change gb.val = _
    rw [he₁, he₂, ← lastDiagonalHom_eq_lift]
    group
  have hcancel := congrArg (fun u : (Mat K (s + 1))ˣ => u * b.val⁻¹) hh
  simpa only [mul_assoc, mul_inv_cancel, mul_one, Subgroup.coe_mul, Subgroup.coe_inv] using hcancel

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicCoset
