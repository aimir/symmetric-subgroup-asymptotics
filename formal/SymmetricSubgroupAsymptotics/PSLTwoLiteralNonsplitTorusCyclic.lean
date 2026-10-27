import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
Actual literal nonsplit torus and cyclicity. Adapted narrowly from
AxiomMath/CFSG 69cb972f587a3ecc035e092253167ff2e303c962,
CharacterTheory/PSL2Table/Basic.lean and
Dihedral/Glauberman/DicksonMaxStructure.lean (Apache-2.0).
No imported CFSG theorem, character theory, classification or order assertion.
-/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitTorusCyclic
variable {F : Type*} [Field F]

private theorem mul_entry (A B : Matrix.SpecialLinearGroup (Fin 2) F) (i j : Fin 2) :
    (A*B).val i j=A.val i 0*B.val 0 j+A.val i 1*B.val 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

/-- Matrices literally of shape [[x,νy],[y,x]], with determinant1. -/
def nonsplitSL (ν : F) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := {A | A.val 1 1=A.val 0 0 ∧ A.val 0 1=ν*A.val 1 0}
  mul_mem' := by
    rintro A B ⟨hA1,hA2⟩ ⟨hB1,hB2⟩
    constructor
    · simp only [mul_entry,hA1,hA2,hB1,hB2]
      ring
    · simp only [mul_entry,hA1,hA2,hB1,hB2]
      ring
  one_mem' := ⟨by simp,by simp⟩
  inv_mem' := by
    rintro A ⟨h1,h2⟩
    constructor
    · simp [Matrix.adjugate_fin_two,h1]
    · simp [Matrix.adjugate_fin_two,h2]

/-- Actual image under the original quotient SL2→PSL2. -/
def nonsplitTorus (ν : F) : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
  (nonsplitSL ν).map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))

theorem nonsplitSL_isCyclic [Finite F] (ν : F) (hν : ¬IsSquare ν) :
    IsCyclic (nonsplitSL ν) := by
  letI : Fact (∀ r : F,r^2≠ν+0*r) := ⟨by
    intro r hr
    apply hν
    exact ⟨r,by simpa only [zero_mul,add_zero,pow_two] using hr.symm⟩⟩
  let ψ : nonsplitSL ν →* QuadraticAlgebra F ν 0 :=
    { toFun := fun A => ⟨A.val.val 0 0,A.val.val 1 0⟩
      map_one' := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
      map_mul' := by
        rintro ⟨A,hA1,hA2⟩ ⟨B,hB1,hB2⟩
        ext
        · simp only [Subgroup.coe_mul,mul_entry,QuadraticAlgebra.re_mul]
          rw [hA2]
        · simp only [Subgroup.coe_mul,mul_entry,QuadraticAlgebra.im_mul]
          rw [hA1]
          ring }
  have hψ : Function.Injective ψ := by
    rintro ⟨A,hA1,hA2⟩ ⟨B,hB1,hB2⟩ h
    have h0 := congrArg QuadraticAlgebra.re h
    have h1 := congrArg QuadraticAlgebra.im h
    change A.val 0 0=B.val 0 0 at h0
    change A.val 1 0=B.val 1 0 at h1
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact h0
    · exact hA2.trans ((congrArg (fun z : F => ν*z) h1).trans hB2.symm)
    · exact h1
    · exact hA1.trans (h0.trans hB1.symm)
  exact isCyclic_of_injective_ringHom ψ hψ

theorem nonsplitTorus_isCyclic [Finite F] (ν : F) (hν : ¬IsSquare ν) :
    IsCyclic (nonsplitTorus ν) := by
  letI : IsCyclic (nonsplitSL ν) := nonsplitSL_isCyclic ν hν
  let f := (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
    (nonsplitSL ν).subtype
  have he : f.range=nonsplitTorus ν := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
    rfl
  rw [←he]
  exact isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective

end SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitTorusCyclic
