import SymmetricSubgroupAsymptotics.CFSGSerreIntegralPathWeights
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootCandidates

/-! Integer source weights and their genuine scalar extensions for EVERY
literal signed D root path. No matrix faithfulness is used. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntegralRootWeights
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGOrthogonalDOriginalRootCandidates
variable (r : ℕ) (hr : 4 ≤ r)

def weight (neg : Bool) (a : Fin r) : RootIndex r→ℤ
  | .inl ij=>
    let start : Fin r:=⟨ij.val.2.val-1,by have h:=ij.val.2.isLt;omega⟩
    let w:=CFSGSerreIntegralPathWeights.pathWeight (CartanMatrix.D r) a start
      (steps r (descend r ij.val.1 start))
    if neg then -w else w
  | .inr ij=>
    let last : Fin r:=⟨r-1,by omega⟩
    let previous : Fin r:=⟨r-2,by omega⟩
    let w:=CFSGSerreIntegralPathWeights.pathWeight (CartanMatrix.D r) a last
      (steps r (descend r ij.val.1 previous ++ descend r ij.val.2 last))
    if neg then -w else w

theorem H_root (neg : Bool) (a : Fin r) (j : RootIndex r) :
    ⁅latticeGenerator (CartanMatrix.D r) (.H a),root r hr neg j⁆=
      weight r hr neg a j • root r hr neg j := by
  cases j <;>
    simpa only [root,difference,sumRoot,path,weight] using
      CFSGSerreIntegralPathWeights.H_scaled_path (CartanMatrix.D r) neg a _ _ _

theorem tensor_H_root (K : Type) [Field K] (neg : Bool) (a : Fin r) (j : RootIndex r) :
    (⁅(1 : K) ⊗ₜ[ℤ] latticeGenerator (CartanMatrix.D r) (.H a),
      (1 : K) ⊗ₜ[ℤ] root r hr neg j⁆ : Space (CartanMatrix.D r) K)=
        (weight r hr neg a j:K) • ((1 : K) ⊗ₜ[ℤ] root r hr neg j) := by
  rw [CFSGSerreIntegralLieAlgebra.spaceBracket_tmul,one_mul,H_root]
  rw [←TensorProduct.smul_tmul,TensorProduct.smul_tmul']
  simp only [←Int.cast_smul_eq_zsmul K,smul_eq_mul,mul_one]

theorem tensor_H_H (K : Type) [Field K] (a b : Fin r) :
    (⁅(1 : K) ⊗ₜ[ℤ] latticeGenerator (CartanMatrix.D r) (.H a),
      (1 : K) ⊗ₜ[ℤ] latticeGenerator (CartanMatrix.D r) (.H b)⁆ : Space (CartanMatrix.D r) K)=0 := by
  have h : (⁅latticeGenerator (CartanMatrix.D r) (.H a),
      latticeGenerator (CartanMatrix.D r) (.H b)⁆ : Source r)=0 := by
    apply Subtype.ext
    exact CFSGSerreLocalNilpotence.generator_HH (CartanMatrix.D r) a b
  rw [CFSGSerreIntegralLieAlgebra.spaceBracket_tmul,h,TensorProduct.tmul_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntegralRootWeights
