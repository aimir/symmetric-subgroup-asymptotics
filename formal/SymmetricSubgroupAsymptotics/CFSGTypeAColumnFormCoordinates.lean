import SymmetricSubgroupAsymptotics.CFSGTypeABlockEmbedding
import SymmetricSubgroupAsymptotics.CFSGTypeAPointRootConjugation
import Mathlib.LinearAlgebra.StdBasis

/-! The exact complementary coordinates of a point-root form. The block
SL action is contragredient on these original coefficients. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTypeAColumnFormCoordinates
open Matrix Module CFSGTypeAProjectivePointRoots CFSGTypeABlockEmbedding
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

def coefficients (f : pointForms (firstVector (F:=F) (n:=n))) : n→F :=
  fun i => f.val (Pi.single (Sum.inr i) 1)

theorem form_apply (f : pointForms (firstVector (F:=F) (n:=n))) (x : Unit ⊕ n→F) :
    f.val x=coefficients f ⬝ᵥ (x∘Sum.inr) := by
  have hx : (∑ i : Unit ⊕ n,x i • Pi.single i (1 : F))=x := by
    simpa only [Pi.basisFun_repr,Pi.basisFun_apply] using
      (Pi.basisFun F (Unit ⊕ n)).sum_repr x
  have hh := congrArg f.val hx
  rw [map_sum] at hh
  rw [←hh]
  simp only [map_smul,smul_eq_mul,Fintype.sum_sum_type,Fintype.sum_unique,
    show f.val (Pi.single (Sum.inl ()) 1)=0 from f.property,mul_zero,zero_add]
  unfold dotProduct coefficients
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem coefficients_injective :
    Function.Injective (coefficients (F:=F) (n:=n)) := by
  intro f g he
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rw [form_apply,form_apply,he]

theorem coefficients_ne_zero {f : pointForms (firstVector (F:=F) (n:=n))}
    (hf : f≠0) : coefficients f≠0 := by
  intro he
  apply hf
  apply coefficients_injective
  simpa only [coefficients,ZeroMemClass.coe_zero,LinearMap.zero_apply] using he

theorem form_comp_block_inverse (A : Matrix.SpecialLinearGroup n F)
    (f : pointForms (firstVector (F:=F) (n:=n))) (x : Unit ⊕ n→F) :
    f.val ((blockHom A).toLin'.symm x)=
      coefficients f ⬝ᵥ (A⁻¹).toLin' (x∘Sum.inr) := by
  have hinv : (blockHom A).toLin'.symm=(blockHom (A⁻¹)).toLin' := by
    simp only [map_inv]
    rfl
  rw [hinv,form_apply,blockHom_apply]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTypeAColumnFormCoordinates
