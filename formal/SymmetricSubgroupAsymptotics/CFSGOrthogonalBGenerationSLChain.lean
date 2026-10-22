import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
import SymmetricSubgroupAsymptotics.CFSGMatrixIdentityExtension
import Mathlib.Algebra.Group.Units.Hom

/-! Literal SL chain matrices inside the actual B elementary group.
Membership follows from the original adjacent B roots and checked SL
generation; no full orthogonal-group identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSLChain
open CFSGOrthogonalBSerreMatrices CFSGTypeAElementaryMatrices
open CFSGMatrixIdentityExtension
variable (K : Type) [Field K] (r : ℕ)

abbrev NaturalSL := Matrix.SpecialLinearGroup (Fin r) K

def doubleHom : NaturalSL K r →* (Mat K r)ˣ :=
  (Units.map (extend K (Fin r ⊕ Fin r) Unit)).comp
    (CFSGOrthogonalDGenerationSLDouble.doubleHom K r)

def chainArray (i j : Fin r) : Mat K r :=
  Matrix.single (pos r i) (pos r j) 1 - Matrix.single (neg r j) (neg r i) 1

theorem doubleHom_elementary_val (i j : Fin r) (hij : i ≠ j) (a : K) :
    ((doubleHom K r (elementary hij a)) : Mat K r) = 1 + a • chainArray K r i j := by
  change extend K (Fin r ⊕ Fin r) Unit
    ((CFSGOrthogonalDGenerationSLDouble.doubleHom K r (elementary hij a)) :
      CFSGOrthogonalDSerreMatrices.Mat K r) = _
  rw [CFSGOrthogonalDGenerationSLDouble.doubleHom_elementary_val]
  ext x y
  rcases x with ((x | x) | ⟨⟩) <;> rcases y with ((y | y) | ⟨⟩) <;>
    simp [extend, chainArray, CFSGOrthogonalDGenerationSLDouble.chainMatrix,
      Matrix.fromBlocks, Matrix.single_apply, Matrix.one_apply, pos, neg]

theorem adjacent_elementary_mem (i j : Fin r) (hij : i ≠ j)
    (hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val) (a : K) :
    doubleHom K r (elementary hij a) ∈ elementaryRootGroup K r := by
  rcases hadj with hp | hn
  · have hi : i.val + 1 < r := by rw [hp]; exact j.isLt
    have hj : (⟨i.val + 1, hi⟩ : Fin r) = j := Fin.ext hp
    have he : doubleHom K r (elementary hij a) = rootTransvection K r false i a := by
      apply Units.ext
      rw [doubleHom_elementary_val, rootTransvection_val]
      simp only [rootMatrix, rootSecond, Bool.false_eq_true, if_false,
        positive, positiveSecond, dif_pos hi, if_pos hi, hj, smul_zero, add_zero]
      rfl
    rw [he]
    exact rootTransvection_mem K r false i a
  · have hj : j.val + 1 < r := by rw [hn]; exact i.isLt
    have hi : (⟨j.val + 1, hj⟩ : Fin r) = i := Fin.ext hn
    have he : doubleHom K r (elementary hij a) = rootTransvection K r true j a := by
      apply Units.ext
      rw [doubleHom_elementary_val, rootTransvection_val]
      simp only [rootMatrix, rootSecond, if_true, negative, negativeSecond,
        dif_pos hj, if_pos hj, hi, smul_zero, add_zero]
      rfl
    rw [he]
    exact rootTransvection_mem K r true j a

theorem doubleHom_range_le : (doubleHom K r).range ≤ elementaryRootGroup K r := by
  let H := (elementaryRootGroup K r).comap (doubleHom K r)
  have ht : H = ⊤ := CFSGOrthogonalDGenerationAdjacentSL.eq_top_of_adjacent r H
    (fun i j hij hadj a => adjacent_elementary_mem K r i j hij hadj a)
  rintro _ ⟨A, rfl⟩
  change A ∈ H
  rw [ht]
  trivial

def doubleIntoElementary : NaturalSL K r →* elementaryRootGroup K r :=
  (doubleHom K r).codRestrict (elementaryRootGroup K r)
    (fun A => doubleHom_range_le K r ⟨A, rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSLChain
