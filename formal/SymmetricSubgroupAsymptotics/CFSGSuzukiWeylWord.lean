import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentGroup
import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusElements

/-! One uniform literal word recovers the Suzuki Weyl matrix from the
two opposite unipotent groups. The calculation uses only zero and one
parameters, uniformly in the original field exponent. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open Matrix CFSG.Models.SuzukiConstruction CFSGSuzukiTorus

theorem weylElement_word (m : ℕ) :
    weylElement m = unipotentElement m 0 1 *
      (weylElement m * unipotentElement m 1 0 * weylElement m) *
        unipotentElement m 1 1 := by
  apply Units.ext
  change weyl m = unipotent m 0 1 *
    (weyl m * unipotent m 1 0 * weyl m) * unipotent m 1 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl,unipotent,Matrix.mul_apply,Fin.sum_univ_succ]

theorem weylElement_mem_opposite_closure (m : ℕ) :
    weylElement m ∈ Subgroup.closure ((unipotentSubgroup m : Set (Ambient m)) ∪
      (unipotentSubgroup m).map (MulAut.conj (weylElement m)).toMonoidHom) := by
  let H := Subgroup.closure ((unipotentSubgroup m : Set (Ambient m)) ∪
    (unipotentSubgroup m).map (MulAut.conj (weylElement m)).toMonoidHom)
  have hU (a b : CFSG.Models.SuzukiConstruction.Field m) : unipotentElement m a b ∈ H :=
    Subgroup.subset_closure (Or.inl ⟨a,b,rfl⟩)
  have hV : weylElement m * unipotentElement m 1 0 * weylElement m ∈ H := by
    apply Subgroup.subset_closure
    apply Or.inr
    refine ⟨unipotentElement m 1 0, ⟨1,0,rfl⟩, ?_⟩
    change weylElement m * unipotentElement m 1 0 * (weylElement m)⁻¹ = _
    rw [weylElement_inv]
  have hprod := H.mul_mem (H.mul_mem (hU 0 1) hV) (hU 1 1)
  exact (congrArg (fun x : Ambient m => x ∈ H) (weylElement_word m).symm).mp hprod

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
