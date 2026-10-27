import SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitTorusCyclic
import SymmetricSubgroupAsymptotics.QuadraticNormKernelCardinality
import Mathlib.Tactic.LinearCombination

/-! The actual quadratic multiplication image equals the literal nonsplit SL2
subgroup; exact cardinality follows from a proved norm-kernel count. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitNormDictionary
open PSLTwoLiteralNonsplitTorusCyclic QuadraticNormOneSpecialLinearEmbedding
variable {F : Type*} [Field F]

theorem quadratic_basis_zero (ν : F) :
    QuadraticAlgebra.basis ν 0 (0 : Fin 2)=(⟨1,0⟩ : QuadraticAlgebra F ν 0) := by
  simp [QuadraticAlgebra.basis,Module.Basis.coe_ofEquivFun,
    QuadraticAlgebra.linearEquivTuple_symm_apply]

theorem quadratic_basis_one (ν : F) :
    QuadraticAlgebra.basis ν 0 (1 : Fin 2)=(⟨0,1⟩ : QuadraticAlgebra F ν 0) := by
  simp [QuadraticAlgebra.basis,Module.Basis.coe_ofEquivFun,
    QuadraticAlgebra.linearEquivTuple_symm_apply]

theorem multiplication_matrix (ν : F) (z : QuadraticAlgebra F ν 0) :
    Algebra.leftMulMatrix (QuadraticAlgebra.basis ν 0) z=!![z.re,ν*z.im;z.im,z.re] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul,QuadraticAlgebra.basis_repr_apply]
  fin_cases i <;> fin_cases j <;>
    simp [quadratic_basis_zero,quadratic_basis_one,QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul]

theorem algebra_norm_formula (ν : F) (z : QuadraticAlgebra F ν 0) :
    Algebra.norm F z=z.re^2-ν*z.im^2 := by
  rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis ν 0),multiplication_matrix,
    Matrix.det_fin_two_of]
  ring

section Field
variable (ν : F) [Fact (∀ r : F,r^2≠ν+0*r)]

/-- A literal equality of actual subgroups, not an abstract torus equivalence. -/
theorem sl_range_eq :
    (slHom (QuadraticAlgebra.basis ν 0)).range=nonsplitSL ν := by
  ext A
  constructor
  · rintro ⟨u,rfl⟩
    change (slHom (QuadraticAlgebra.basis ν 0) u).val 1 1=
      (slHom (QuadraticAlgebra.basis ν 0) u).val 0 0 ∧
      (slHom (QuadraticAlgebra.basis ν 0) u).val 0 1=
        ν*(slHom (QuadraticAlgebra.basis ν 0) u).val 1 0
    simp [slHom_matrix,multiplication_matrix]
  · rintro ⟨h11,h01⟩
    let z : QuadraticAlgebra F ν 0 := ⟨A.val 0 0,A.val 1 0⟩
    have hz : Algebra.norm F z=1 := by
      rw [algebra_norm_formula]
      have hd := A.property
      rw [Matrix.det_fin_two,h11,h01] at hd
      change A.val 0 0^2-ν*A.val 1 0^2=1
      linear_combination hd
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0,Algebra.norm_zero] at hz
      exact zero_ne_one hz
    let u : (QuadraticAlgebra F ν 0)ˣ := Units.mk0 z hz0
    have hu : u ∈ NormOne F (QuadraticAlgebra F ν 0) := by
      apply Units.ext
      exact hz
    refine ⟨⟨u,hu⟩,?_⟩
    apply Subtype.ext
    rw [slHom_matrix,multiplication_matrix]
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact h01.symm
    · rfl
    · exact h11.symm

end Field

theorem card_nonsplitSL [Finite F] (ν : F) (hν : ¬IsSquare ν) :
    Nat.card (nonsplitSL ν)=Nat.card F+1 := by
  letI : Fact (∀ r : F,r^2≠ν+0*r) := ⟨by
    intro r hr
    exact hν ⟨r,by simpa only [zero_mul,add_zero,pow_two] using hr.symm⟩⟩
  letI : Finite (QuadraticAlgebra F ν 0) :=
    Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd ν 0).symm
  rw [←sl_range_eq ν,card_sl_range]
  exact QuadraticNormKernelCardinality.norm_one_card (QuadraticAlgebra.basis ν 0)

end SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitNormDictionary
