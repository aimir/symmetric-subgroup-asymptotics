import SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineHom
import SymmetricSubgroupAsymptotics.CFSGSymplecticAdditiveOrbitIndex
import SymmetricSubgroupAsymptotics.CFSGTypeAVectorTransitivity
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Lean.Elab.Tactic.Omega

/-! The actual natural pairing is a nondegenerate bilinear form, and
the actual elementary group is transitive on nonzero vectors in every
positive rank. Rank one is discharged by determinant-one two-coordinate
normalization, rather than applying the higher-rank theorem there. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalBilinearClassGeometry
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticStabilizerCoordinates
variable (K : Type) [Field K]

def naturalPairing (r : ℕ) : LinearMap.BilinForm K (Index r → K) where
  toFun v := {
    toFun w := pairing r v w
    map_add' w z := pairing_add_right r v w z
    map_smul' a w := pairing_smul_right r a v w }
  map_add' v w := by
    apply LinearMap.ext
    intro z
    exact pairing_add_left r v w z
  map_smul' a v := by
    apply LinearMap.ext
    intro w
    exact pairing_smul_left r a v w

theorem naturalPairing_apply (r : ℕ) (v w : Index r → K) :
    naturalPairing K r v w = pairing r v w := rfl

theorem naturalPairing_nondegenerate (r : ℕ) : (naturalPairing K r).Nondegenerate := by
  constructor
  · intro v hv
    funext i
    cases i with
    | inl i =>
      have h := hv (Pi.single (Sum.inr i) 1)
      change pairing r v (Pi.single (Sum.inr i) 1) = 0 at h
      rw [pairing_neg_basis] at h
      exact h
    | inr i =>
      have h := hv (Pi.single (Sum.inl i) 1)
      change pairing r v (Pi.single (Sum.inl i) 1) = 0 at h
      rw [pairing_pos_basis] at h
      exact neg_eq_zero.mp h
  · intro w hw
    funext i
    cases i with
    | inl i =>
      have h := hw (Pi.single (Sum.inr i) 1)
      change pairing r (Pi.single (Sum.inr i) 1) w = 0 at h
      rw [pairing_neg_basis_left] at h
      exact neg_eq_zero.mp h
    | inr i =>
      have h := hw (Pi.single (Sum.inl i) 1)
      change pairing r (Pi.single (Sum.inl i) 1) w = 0 at h
      rw [pairing_pos_basis_left] at h
      exact h

theorem exists_map_nonzero (r : ℕ) (hr : 0 < r)
    (v w : Index r → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : elementaryRootGroup K r, (g.val : Mat K r) *ᵥ v = w := by
  cases r with
  | zero => omega
  | succ s =>
    cases s with
    | zero =>
      obtain ⟨g,hg⟩ := CFSGTypeAVectorTransitivity.exists_map_nonzero
        (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 1)) (by intro h; cases h) v w hv hw
      refine ⟨⟨Matrix.SpecialLinearGroup.toGL g,rankOne_SL_toGL_mem K g⟩, ?_⟩
      exact hg
    | succ s =>
      exact CFSGSymplecticAdditiveOrbitIndex.exists_map_nonzero K (s+1)
        (Nat.succ_pos s) v w hv hw

end SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalBilinearClassGeometry
