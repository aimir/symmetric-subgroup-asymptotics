import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices

/-! Inverse-transpose on actual matrix units, with a signed-monomial
fixedness criterion. No isometry or group-recognition premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMatrixUnitInverseTranspose
variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

def inverseTranspose : (Matrix I I R)ˣ →* (Matrix I I R)ˣ where
  toFun u := {
    val := (u⁻¹).val.transpose
    inv := u.val.transpose
    val_inv := by
      rw [←Matrix.transpose_mul,←Units.val_mul,mul_inv_cancel,Units.val_one,
        Matrix.transpose_one]
    inv_val := by
      rw [←Matrix.transpose_mul,←Units.val_mul,inv_mul_cancel,Units.val_one,
        Matrix.transpose_one] }
  map_one' := by
    apply Units.ext
    simp only [inv_one,Units.val_one,Matrix.transpose_one]
  map_mul' u v := by
    apply Units.ext
    simp only [mul_inv_rev,Units.val_mul,Matrix.transpose_mul]

theorem inverseTranspose_val (u : (Matrix I I R)ˣ) :
    (inverseTranspose u).val=(u⁻¹).val.transpose := rfl

theorem inverseTranspose_inv_val (u : (Matrix I I R)ˣ) :
    ((inverseTranspose u)⁻¹).val=u.val.transpose := rfl

theorem inverseTranspose_involutive :
    Function.Involutive (inverseTranspose (I:=I) (R:=R)) := by
  intro u
  apply Units.ext
  change u.val.transpose.transpose=u.val
  exact Matrix.transpose_transpose u.val

private theorem monomial_mul_transpose (s : Equiv.Perm I) (d : I→R)
    (hd : ∀i,d i*d i=1) :
    CFSGTypeAMonomialMatrices.monomial s d*
      (CFSGTypeAMonomialMatrices.monomial s d).transpose=1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,
    CFSGTypeAMonomialMatrices.monomial_apply]
  rw [Finset.sum_eq_single (s i)]
  · by_cases hij : i=j
    · subst j
      simp [hd]
    · have hs : s j≠s i := fun he=>hij (s.injective he).symm
      simp [hij,hs]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem inverseTranspose_monomial (u : (Matrix I I R)ˣ) (s : Equiv.Perm I)
    (d : I→R) (hu : u.val=CFSGTypeAMonomialMatrices.monomial s d)
    (hd : ∀i,d i*d i=1) : inverseTranspose u=u := by
  have hm : u.val*u.val.transpose=1 := by
    rw [hu]
    exact monomial_mul_transpose s d hd
  have hinv : (u⁻¹).val*u.val=1 := by
    rw [←Units.val_mul,inv_mul_cancel,Units.val_one]
  have he : (u⁻¹).val=u.val.transpose := by
    calc
      (u⁻¹).val=(u⁻¹).val*1 := (mul_one _).symm
      _=(u⁻¹).val*(u.val*u.val.transpose) := by rw [hm]
      _=((u⁻¹).val*u.val)*u.val.transpose := (mul_assoc _ _ _).symm
      _=u.val.transpose := by rw [hinv,one_mul]
  apply Units.ext
  change (u⁻¹).val.transpose=u.val
  rw [he,Matrix.transpose_transpose]

end SymmetricSubgroupAsymptotics.CFSGMatrixUnitInverseTranspose
