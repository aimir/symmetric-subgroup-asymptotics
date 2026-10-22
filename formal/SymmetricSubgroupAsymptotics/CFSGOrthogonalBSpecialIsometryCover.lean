import SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicCoset
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMaximalSubspaceOrbit
import SymmetricSubgroupAsymptotics.CFSGMatrixSubspaceUnitAction
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction

/-! Every actual determinant-one B isometry lies in a last-pair diagonal
coset of the SAME original elementary subgroup. We normalize the inverse
image of V⁺ and then use right-hand parabolic factorization. No normality
of E, Omega identification or group order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialIsometryCover
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIndexForm CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBPositiveSubspace CFSGOrthogonalBLastDiagonal
open CFSGPolarSubspacePoints
variable (K : Type) [Field K] [Finite K]

theorem special_one_sided_factor (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (g : specialFormUnits K (s + 1)) :
    ∃ t : Kˣ, ∃ e : elementaryRootGroup K (s + 1), g.val = lastDiagonalHom K s t * e.val := by
  let gi : formUnits K (s + 1) :=
    ⟨g.val⁻¹, ((specialFormUnits K (s + 1)).inv_mem g.property).1⟩
  let ei := CFSGProjectiveLinearPointAction.linearEquiv gi.val
  let P₀ : Subspaces (gram K (s + 1)).toBilin' :=
    ⟨positiveSubspace K (s + 1), positiveSubspace_singular K (s + 1)⟩
  let P := isometrySubspace (gram K (s + 1)).toBilin' ei
    (fun x y => pairing_invariant K (s + 1) gi x y) P₀
  have hdim : Module.finrank K P.val = s + 1 :=
    (isometrySubspace_finrank (gram K (s + 1)).toBilin' ei
      (fun x y => pairing_invariant K (s + 1) gi x y) P₀).trans
        (positiveSubspace_finrank K (s + 1))
  obtain ⟨a, ha⟩ := CFSGOrthogonalBMaximalSubspaceOrbit.exists_normalize_full_rank K h2 (s + 1) P hdim
  change ((positiveSubspace K (s + 1)).map
    (Matrix.mulVecLin ((g.val⁻¹ : (Mat K (s + 1))ˣ) : Mat K (s + 1)))).map
      (Matrix.mulVecLin (a.val : Mat K (s + 1))) = positiveSubspace K (s + 1) at ha
  have hforward : (positiveSubspace K (s + 1)).map
      (Matrix.mulVecLin ((a.val * g.val⁻¹ : (Mat K (s + 1))ˣ) : Mat K (s + 1))) =
        positiveSubspace K (s + 1) := by
    rw [CFSGMatrixSubspaceUnitAction.map_mul]
    exact ha
  have hinv := CFSGMatrixSubspaceUnitAction.invariant_inverse
    (positiveSubspace K (s + 1)) (a.val * g.val⁻¹) hforward
  let ga : specialFormUnits K (s + 1) :=
    ⟨g.val * a.val⁻¹, (specialFormUnits K (s + 1)).mul_mem g.property
      ((specialFormUnits K (s + 1)).inv_mem
        (elementary_le_specialFormUnits K p h2 (s + 1) a.property))⟩
  have hga : (positiveSubspace K (s + 1)).map
      (Matrix.mulVecLin (ga.val : Mat K (s + 1))) = positiveSubspace K (s + 1) := by
    simpa only [mul_inv_rev, inv_inv] using hinv
  obtain ⟨t, e, he⟩ := CFSGOrthogonalBParabolicCoset.parabolic_one_sided_factor K p h2 s ga hga
  refine ⟨t, e * a, ?_⟩
  have hh := congrArg (fun u : (Mat K (s + 1))ˣ => u * a.val) he
  change (g.val * a.val⁻¹) * a.val = (lastDiagonalHom K s t * e.val) * a.val at hh
  simpa only [mul_assoc, inv_mul_cancel, mul_one, Subgroup.coe_mul] using hh

theorem special_one_sided_cover (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (g : specialFormUnits K (s + 1)) :
    ∃ t : Kˣ, (lastDiagonalHom K s t)⁻¹ * g.val ∈ elementaryRootGroup K (s + 1) := by
  obtain ⟨t, e, he⟩ := special_one_sided_factor K p h2 s g
  refine ⟨t, ?_⟩
  rw [he, inv_mul_cancel_left]
  exact e.property

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialIsometryCover
