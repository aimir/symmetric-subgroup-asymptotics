import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalDeterminant
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationAdjacentSL

/-! The literal natural adjacent-root group is the actual special linear
matrix group, over every field. This is proved by elementary generation,
not by a group-name identification or source simplicity. It gives actual
natural-group membership for determinant-one matrix constructions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSGTypeAElementaryMatrices CFSGSerreSquareZeroMatrix
variable (K : Type) [Field K] (r : ℕ)

abbrev NaturalSL := Matrix.SpecialLinearGroup (Fin (r + 1)) K

theorem specialLinear_toGL_mem (g : NaturalSL K r) :
    Matrix.SpecialLinearGroup.toGL g ∈ NaturalElementary K r := by
  let H : Subgroup (NaturalSL K r) :=
    (NaturalElementary K r).comap Matrix.SpecialLinearGroup.toGL
  have htop : H = ⊤ := by
    apply CFSGOrthogonalDGenerationAdjacentSL.eq_top_of_adjacent (r + 1)
    intro i j hij hnear a
    change Matrix.SpecialLinearGroup.toGL (elementary hij a) ∈ NaturalElementary K r
    rcases hnear with hnear | hnear
    · let k : Fin r := ⟨i.val, by have hj := j.isLt; omega⟩
      have hi : k.castSucc = i := Fin.ext rfl
      have hj : k.succ = j := Fin.ext hnear
      have he : Matrix.SpecialLinearGroup.toGL (elementary hij a) =
          naturalRootUnit K r false k a := by
        apply Units.ext
        change 1 + Matrix.single i j a = 1 + a • positive K r k
        simp only [positive, Matrix.smul_single, smul_eq_mul, mul_one, hi, hj]
      rw [he]
      exact (elementaryRoot K (naturalRootUnit K r) false k a).property
    · let k : Fin r := ⟨j.val, by have hi := i.isLt; omega⟩
      have hj : k.castSucc = j := Fin.ext rfl
      have hi : k.succ = i := Fin.ext hnear
      have he : Matrix.SpecialLinearGroup.toGL (elementary hij a) =
          naturalRootUnit K r true k a := by
        apply Units.ext
        change 1 + Matrix.single i j a = 1 + a • negative K r k
        simp only [negative, positive, Matrix.transpose_single,
          Matrix.smul_single, smul_eq_mul, mul_one, hi, hj]
      rw [he]
      exact (elementaryRoot K (naturalRootUnit K r) true k a).property
  have hg : g ∈ H := by rw [htop]; trivial
  exact hg

def specialLinearToNatural : NaturalSL K r →* NaturalElementary K r where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g, specialLinear_toGL_mem K r g⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

def naturalToSpecialLinear : NaturalElementary K r →* NaturalSL K r where
  toFun u := ⟨(u.val : Mat K r), naturalElementary_det K r u⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' u v := by apply Subtype.ext; rfl

def naturalSpecialLinearEquiv : NaturalElementary K r ≃* NaturalSL K r where
  __ := naturalToSpecialLinear K r
  invFun := specialLinearToNatural K r
  left_inv u := by apply Subtype.ext; apply Units.ext; rfl
  right_inv g := by apply Subtype.ext; rfl

theorem unit_mem_natural_of_det (u : (Mat K r)ˣ) (hu : Matrix.det (u : Mat K r) = 1) :
    u ∈ NaturalElementary K r := by
  let g : NaturalSL K r := ⟨(u : Mat K r), hu⟩
  have he : Matrix.SpecialLinearGroup.toGL g = u := by apply Units.ext; rfl
  exact he ▸ specialLinear_toGL_mem K r g

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
