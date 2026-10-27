import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalTensorRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntegralRootWeights
import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroLieRealization

/-! The natural realization of the SAME original D tensor Lie algebra has
CENTRAL kernel in every field, including characteristic two. Primitive
root entries first force a kernel vector into the original Cartan span.
Actual integer path weights make its brackets lie in single root lines;
those lines remain primitive after reduction, so their brackets vanish.
No ambient-injectivity, root-table or source-faithfulness premise occurs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalAmbientKernelCentral
open CFSG.Models.Chevalley CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDOriginalRootCandidates CFSGOrthogonalDOriginalIntegralBasis
open CFSGOrthogonalDOriginalTensorRootCoordinates CFSGOrthogonalDOriginalIntegralRootWeights
variable (r : ℕ) (hr : 4 ≤ r) (K : Type) [Field K]

private theorem intrinsic_skew {S : Type*} [LieRing S] (x y : S) :
    ⁅x,y⁆ = -⁅y,x⁆ := by
  have h := LieRing.lie_self (x+y)
  rw [LieRing.add_lie,LieRing.lie_add,LieRing.lie_add,
    LieRing.lie_self,LieRing.lie_self,zero_add,add_zero] at h
  exact eq_neg_iff_add_eq_zero.mpr h

private theorem intrinsic_smul_lie {S : Type*} [LieRing S] [LieAlgebra K S]
    (a : K) (x y : S) : ⁅a • x,y⁆ = a • ⁅x,y⁆ := by
  rw [intrinsic_skew (a • x) y,LieAlgebra.lie_smul,←smul_neg,
    ←intrinsic_skew x y]

private theorem intrinsic_sum_lie {S : Type*} [LieRing S] {I : Type*}
    (s : Finset I) (f : I → S) (y : S) : ⁅∑ i ∈ s,f i,y⁆ = ∑ i ∈ s,⁅f i,y⁆ :=
  map_sum (AddMonoidHom.mk' (fun x : S => ⁅x,y⁆)
    (fun x z => LieRing.add_lie x z y)) f s

private theorem intrinsic_lie_sum {S : Type*} [LieRing S] {I : Type*}
    (s : Finset I) (f : I → S) (x : S) : ⁅x,∑ i ∈ s,f i⁆ = ∑ i ∈ s,⁅x,f i⁆ :=
  map_sum (AddMonoidHom.mk' (fun y : S => ⁅x,y⁆)
    (LieRing.lie_add x)) f s

private theorem root_image (neg : Bool) (j : RootIndex r) :
    orthogonalBaseChange K r hr ((1 : K) ⊗ₜ[ℤ] root r hr neg j)=
      CFSGOrthogonalDUniformRootCoordinates.matrix K r (neg,j) := by
  have h:=tensorBasis_image r hr K (.inr (neg,j))
  rw [tensorBasis_apply] at h
  exact h

private theorem root_line_zero (neg : Bool) (j : RootIndex r) (a : K)
    (h : orthogonalBaseChange K r hr (a • ((1 : K) ⊗ₜ[ℤ] root r hr neg j))=0) : a=0 := by
  rw [map_smul,root_image] at h
  have hc:=congrArg (CFSGOrthogonalDUniformRootCoordinates.coordinates K r) h
  rw [map_smul,CFSGOrthogonalDUniformRootCoordinates.coordinates_matrix,map_zero] at hc
  have hj:=congrFun hc (neg,j)
  simpa only [Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one,Pi.zero_apply] using hj

private theorem kernel_bracket_cartan (x : Space (CartanMatrix.D r) K)
    (hx : orthogonalBaseChange K r hr x=0) (b : Fin r) :
    ⁅x,(1 : K) ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.D r) (.H b)⁆=0 := by
  rw [kernel_eq_cartan_combination r hr K x hx,intrinsic_sum_lie]
  apply Finset.sum_eq_zero
  intro a ha
  rw [intrinsic_smul_lie K ((tensorBasis r hr K).repr x (.inl a))
    ((1 : K) ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.D r) (.H a))
    ((1 : K) ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.D r) (.H b)),
    tensor_H_H,smul_zero]

private theorem kernel_bracket_root (x : Space (CartanMatrix.D r) K)
    (hx : orthogonalBaseChange K r hr x=0) (neg : Bool) (j : RootIndex r) :
    ⁅x,(1 : K) ⊗ₜ[ℤ] root r hr neg j⁆=0 := by
  let mu : K:=∑ a : Fin r,(tensorBasis r hr K).repr x (.inl a)*(weight r hr neg a j:K)
  have he : ⁅x,(1 : K) ⊗ₜ[ℤ] root r hr neg j⁆=mu • ((1 : K) ⊗ₜ[ℤ] root r hr neg j) := by
    conv_lhs => rw [kernel_eq_cartan_combination r hr K x hx]
    rw [intrinsic_sum_lie]
    change (∑ a : Fin r, ⁅(tensorBasis r hr K).repr x (.inl a) •
      ((1 : K) ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.D r) (.H a)),
      (1 : K) ⊗ₜ[ℤ] root r hr neg j⁆) = _
    trans ∑ a : Fin r, ((tensorBasis r hr K).repr x (.inl a) *
      (weight r hr neg a j : K)) • ((1 : K) ⊗ₜ[ℤ] root r hr neg j)
    · apply Finset.sum_congr rfl
      intro a ha
      rw [intrinsic_smul_lie K ((tensorBasis r hr K).repr x (.inl a))
        ((1 : K) ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.D r) (.H a))
        ((1 : K) ⊗ₜ[ℤ] root r hr neg j),tensor_H_root,smul_smul]
    · change (∑ a : Fin r, ((tensorBasis r hr K).repr x (.inl a) *
        (weight r hr neg a j : K)) • ((1 : K) ⊗ₜ[ℤ] root r hr neg j)) =
          (∑ a : Fin r, (tensorBasis r hr K).repr x (.inl a) *
            (weight r hr neg a j : K)) • ((1 : K) ⊗ₜ[ℤ] root r hr neg j)
      rw [Finset.sum_smul]
  have hz : orthogonalBaseChange K r hr ⁅x,(1 : K) ⊗ₜ[ℤ] root r hr neg j⁆=0 := by
    rw [CFSGSerreSquareZeroLieRealization.baseChange_map_lie (realizationData r hr) K,hx,zero_lie]
  rw [he] at hz
  have hm:=root_line_zero r hr K neg j mu hz
  rw [he,hm,zero_smul]

/-- Pointwise central-kernel form consumed by PerfectLieCentralDeviation. -/
theorem kernel_central (x : Space (CartanMatrix.D r) K)
    (hx : orthogonalBaseChange K r hr x=0) (y : Space (CartanMatrix.D r) K) : ⁅x,y⁆=0 := by
  conv_lhs => rw [←tensor_expansion r hr K y]
  rw [intrinsic_lie_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [LieAlgebra.lie_smul ((tensorBasis r hr K).repr y j) x
    ((1 : K) ⊗ₜ[ℤ] vector r hr j)]
  rcases j with b | ⟨neg,j⟩
  · rw [show vector r hr (.inl b)=CFSGSerreDiagram.latticeGenerator (CartanMatrix.D r) (.H b) from rfl,
      kernel_bracket_cartan r hr K x hx b,smul_zero]
  · rw [show vector r hr (.inr (neg,j))=root r hr neg j from rfl,
      kernel_bracket_root r hr K x hx neg j,smul_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalAmbientKernelCentral
