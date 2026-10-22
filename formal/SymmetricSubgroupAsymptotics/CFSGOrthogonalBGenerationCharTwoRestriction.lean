import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationBlockRestriction
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryGroup
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.CharP.Two

/-! Characteristic-two restriction of the literal B matrices to the
invariant 2r-coordinate hyperplane. The quadratic terminal parameter
becomes t² in the actual C root subgroup; no scalar-commutant assertion
for the reducible odd-dimensional representation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoRestriction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationElements
open CFSGOrthogonalBGenerationBlockRestriction
variable (K : Type) [Field K] [CharP K 2]

theorem root_fixedLastRow (r : ℕ) (neg : Bool) (i : Fin r) (t : K) :
    FixedLastRow K (Fin r ⊕ Fin r) (rootTransvection K r neg i t : Mat K r) := by
  intro j
  by_cases hi : i.val + 1 < r
  all_goals
    cases neg <;> rcases j with ((j | j) | ⟨⟩) <;>
      simp [rootTransvection_val, rootMatrix, rootSecond, positive, negative,
        positiveSecond, negativeSecond, hi, pos, neg, middle,
        Matrix.single_apply, Matrix.one_apply, CharTwo.two_eq_zero]

theorem elementary_le_rowSubgroup (r : ℕ) :
    elementaryRootGroup K r ≤ rowSubgroup K (Fin r ⊕ Fin r) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨neg, i, t, rfl⟩
  exact root_fixedLastRow K r neg i t

def naturalRestriction (r : ℕ) : elementaryRootGroup K r →*
    (CFSGSymplecticSerreMatrices.Mat K r)ˣ :=
  (upperBlockHom K (Fin r ⊕ Fin r)).comp (Subgroup.inclusion (elementary_le_rowSubgroup K r))

theorem root_upperBlock (r : ℕ) (neg : Bool) (i : Fin r) (t : K) :
    upperBlock K (Fin r ⊕ Fin r) (rootTransvection K r neg i t : Mat K r) =
      (CFSGSymplecticSerreMatrices.rootTransvection K r neg i
        (if i.val + 1 < r then t else t ^ 2) : CFSGSymplecticSerreMatrices.Mat K r) := by
  by_cases hi : i.val + 1 < r
  all_goals
    cases neg <;> ext x y <;> cases x <;> cases y <;>
      simp [upperBlock, rootTransvection_val, rootMatrix, rootSecond, positive, negative,
        positiveSecond, negativeSecond, CFSGSymplecticSerreMatrices.rootTransvection_val,
        CFSGSymplecticSerreMatrices.rootMatrix, CFSGSymplecticSerreMatrices.positive,
        CFSGSymplecticSerreMatrices.negative, hi, pos, neg, middle,
        Matrix.transpose_apply, Matrix.single_apply, Matrix.one_apply,
        Matrix.smul_apply, CharTwo.two_eq_zero, CharTwo.neg_eq]

theorem naturalRestriction_root (r : ℕ) (neg : Bool) (i : Fin r) (t : K) :
    naturalRestriction K r (rootElement K r neg i t) =
      CFSGSymplecticSerreMatrices.rootTransvection K r neg i
        (if i.val + 1 < r then t else t ^ 2) := by
  apply Units.ext
  exact root_upperBlock K r neg i t

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoRestriction
