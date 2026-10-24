import SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineCoordinates
import SymmetricSubgroupAsymptotics.MatrixUnitBilinearIsometryOrderBound
import SymmetricSubgroupAsymptotics.LinearSemidirectCommutingFibres

/-! The actual elementary first-vector stabilizer maps to the natural
affine group on the smaller symplectic space. Tail restriction and the
partner column are literal original matrix coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineHom
open CFSGSymplecticSerreMatrices CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticPointTailCoordinates CFSGSymplecticPointAffineCoordinates
open LinearSemidirectCommutingFibres
variable (K : Type) [Field K]

def pointStabilizer (r : ℕ) : Subgroup (elementaryRootGroup K (r+1)) where
  carrier := {g | FixesFirstVector K r (g.val : Mat K (r+1))}
  one_mem' := Matrix.one_mulVec _
  mul_mem' := by
    intro g h hg hh
    change ((g.val : Mat K (r+1)) * (h.val : Mat K (r+1))) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hh, hg]
  inv_mem' := by
    intro g hg
    change ((g⁻¹).val : Mat K (r+1)) *ᵥ _ = _
    calc
      _ = ((g⁻¹).val : Mat K (r+1)) *ᵥ
          ((g.val : Mat K (r+1)) *ᵥ Pi.single (Sum.inl 0) 1) := by rw [hg]
      _ = (((g⁻¹).val : Mat K (r+1)) * (g.val : Mat K (r+1))) *ᵥ _ :=
        Matrix.mulVec_mulVec _ _ _
      _ = _ := by
        have he := congrArg (fun a : elementaryRootGroup K (r+1) =>
          (a.val : Mat K (r+1))) (inv_mul_cancel g)
        change ((g⁻¹).val : Mat K (r+1)) * (g.val : Mat K (r+1)) = 1 at he
        rw [he, Matrix.one_mulVec]

private theorem point_preserves (r : ℕ) (g : pointStabilizer K r) :
    PreservesPairing (r+1) (g.val.val : Mat K (r+1)) :=
  preservesPairing_of_form (r+1) _
    (elementaryRootGroup_le_formPreserving K (r+1) g.val.property)

def pointTailUnits (r : ℕ) (g : pointStabilizer K r) : (Mat K r)ˣ where
  val := tailMatrix r (g.val.val : Mat K (r+1))
  inv := tailMatrix r ((g⁻¹).val.val : Mat K (r+1))
  val_inv := by
    rw [← tailMatrix_mul_of_fixed_first K r _ _ g.property
      (point_preserves K r (g⁻¹)) (g⁻¹).property]
    have he := congrArg (fun a : pointStabilizer K r =>
      (a.val.val : Mat K (r+1))) (mul_inv_cancel g)
    change (g.val.val : Mat K (r+1)) * ((g⁻¹).val.val : Mat K (r+1)) = 1 at he
    rw [he, tailMatrix_one]
  inv_val := by
    rw [← tailMatrix_mul_of_fixed_first K r _ _ (g⁻¹).property
      (point_preserves K r g) g.property]
    have he := congrArg (fun a : pointStabilizer K r =>
      (a.val.val : Mat K (r+1))) (inv_mul_cancel g)
    change ((g⁻¹).val.val : Mat K (r+1)) * (g.val.val : Mat K (r+1)) = 1 at he
    rw [he, tailMatrix_one]

def pointTailHom (r : ℕ) : pointStabilizer K r →* elementaryRootGroup K r where
  toFun g := ⟨pointTailUnits K r g, all_formPreserving_elementary K r _
    (tailMatrix_preserves_pairing_of_fixed_first K r _
      (point_preserves K r g) g.property)⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact tailMatrix_one r
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    exact tailMatrix_mul_of_fixed_first K r _ _ g.property
      (point_preserves K r h) h.property

theorem pointTailHom_val (r : ℕ) (g : pointStabilizer K r) :
    ((pointTailHom K r g).val : Mat K r) =
      tailMatrix r (g.val.val : Mat K (r+1)) := rfl

def naturalLinearHom (r : ℕ) :
    elementaryRootGroup K r →* ((Index r → K) ≃ₗ[K] (Index r → K)) :=
  MatrixUnitBilinearIsometryOrderBound.naturalLinearHom K (Index r)
    (elementaryRootGroup K r)

def pointAffineHom (r : ℕ) : pointStabilizer K r →*
    AffineGroup (naturalLinearHom K r) where
  toFun g := ⟨Multiplicative.ofAdd (partnerColumn K r (g.val.val : Mat K (r+1))),
    pointTailHom K r g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      cases i <;> simp [partnerColumn, tailIndex]
    · exact (pointTailHom K r).map_one
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change partnerColumn K r
          ((g.val.val : Mat K (r+1)) * (h.val.val : Mat K (r+1))) =
        partnerColumn K r (g.val.val : Mat K (r+1)) +
          tailMatrix r (g.val.val : Mat K (r+1)) *ᵥ
            partnerColumn K r (h.val.val : Mat K (r+1))
      exact partnerColumn_mul K r _ _ g.property (point_preserves K r h) h.property
    · exact (pointTailHom K r).map_mul g h

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointAffineHom
