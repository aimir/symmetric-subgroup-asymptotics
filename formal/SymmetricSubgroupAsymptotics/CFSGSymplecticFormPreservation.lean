import SymmetricSubgroupAsymptotics.CFSGSymplecticInfinitesimalForm
import SymmetricSubgroupAsymptotics.CFSGSquareZeroFormPreservation
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryGroup

/-! The same literal elementary root matrices preserve the standard
alternating form. Their natural action embeds in mathlib's symplectic
group; surjectivity onto that full group is not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable (R : Type*) [CommRing R]

theorem rootMatrix_infinitesimal (r : ℕ) (neg : Bool) (i : Fin r) :
    rootMatrix R r neg i * Matrix.J (Fin r) R +
      Matrix.J (Fin r) R * (rootMatrix R r neg i).transpose = 0 := by
  cases neg
  · exact positive_infinitesimal R r i
  · exact negative_infinitesimal R r i

theorem rootTransvection_preserves_form (r : ℕ) (neg : Bool) (i : Fin r) (t : R) :
    (rootTransvection R r neg i t : Mat R r) * Matrix.J (Fin r) R *
      (rootTransvection R r neg i t : Mat R r).transpose = Matrix.J (Fin r) R :=
  CFSGSquareZeroFormPreservation.transvection_preserves _ _
    (rootMatrix_sq_zero R r neg i) (rootMatrix_infinitesimal R r neg i) t

theorem inverse_preserves_form (r : ℕ) (u : (Mat R r)ˣ)
    (hu : (u : Mat R r) * Matrix.J (Fin r) R * (u : Mat R r).transpose =
      Matrix.J (Fin r) R) :
    (↑(u⁻¹) : Mat R r) * Matrix.J (Fin r) R * (↑(u⁻¹) : Mat R r).transpose =
      Matrix.J (Fin r) R := by
  calc
    (↑(u⁻¹) : Mat R r) * Matrix.J (Fin r) R * (↑(u⁻¹) : Mat R r).transpose =
        (↑(u⁻¹) : Mat R r) *
          ((u : Mat R r) * Matrix.J (Fin r) R * (u : Mat R r).transpose) *
          (↑(u⁻¹) : Mat R r).transpose := by rw [hu]
    _ = ((↑(u⁻¹) : Mat R r) * (u : Mat R r)) * Matrix.J (Fin r) R *
        ((u : Mat R r).transpose * (↑(u⁻¹) : Mat R r).transpose) := by
      simp only [mul_assoc]
    _ = Matrix.J (Fin r) R := by
      have hc : (↑(u⁻¹) : Mat R r) * (u : Mat R r) = 1 := Units.inv_mul u
      rw [← Matrix.transpose_mul, hc, Matrix.transpose_one, one_mul, mul_one]

def formPreservingUnits (r : ℕ) : Subgroup ((Mat R r)ˣ) where
  carrier := {u | (u : Mat R r) * Matrix.J (Fin r) R * (u : Mat R r).transpose =
    Matrix.J (Fin r) R}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ((u : Mat R r) * (v : Mat R r)) * Matrix.J (Fin r) R *
      ((u : Mat R r) * (v : Mat R r)).transpose = Matrix.J (Fin r) R
    rw [Matrix.transpose_mul]
    calc
      _ = (u : Mat R r) *
          ((v : Mat R r) * Matrix.J (Fin r) R * (v : Mat R r).transpose) *
          (u : Mat R r).transpose := by simp only [mul_assoc]
      _ = Matrix.J (Fin r) R := by rw [hv, hu]
  inv_mem' := by
    intro u hu
    exact inverse_preserves_form R r u hu

theorem elementaryRootGroup_le_formPreserving (r : ℕ) :
    elementaryRootGroup R r ≤ formPreservingUnits R r := by
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨neg, i, t, rfl⟩
  exact rootTransvection_preserves_form R r neg i t

def elementaryToSymplectic (r : ℕ) :
    elementaryRootGroup R r →* Matrix.symplecticGroup (Fin r) R where
  toFun u := ⟨(u.val : Mat R r), elementaryRootGroup_le_formPreserving R r u.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem elementaryToSymplectic_injective (r : ℕ) :
    Function.Injective (elementaryToSymplectic R r) := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
