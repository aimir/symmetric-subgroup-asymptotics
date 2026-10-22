import SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieFirstLayer
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-! Actual triangular decomposition plus height-one projection extracts
the original negative-generator linear span. Positive and diagonal
summands have zero negative first layer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieTriangularLayer
open CFSGGradedMatrixSupport CFSGGradedMatrixLieFirstLayer
variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

omit [Fintype I] [DecidableEq I] in
theorem firstPart_opposite_zero (weight : I→ℤ) (M : Matrix I I K)
    (hM : Positive weight M) : firstPart (fun i=> -weight i) M=0 := by
  ext i j
  rw [firstPart_apply]
  by_cases h : -weight i= -weight j+1
  · rw [if_pos h,hM i j (by omega)]
    rfl
  · rw [if_neg h]
    rfl

theorem firstPart_diagonal_zero (weight : I→ℤ) (M : Matrix I I K)
    (hM : M.IsDiag) : firstPart weight M=0 := by
  ext i j
  rw [firstPart_apply]
  by_cases h : weight i=weight j+1
  · have hij : i≠j := by intro he;subst j;omega
    rw [if_pos h,hM hij]
    rfl
  · rw [if_neg h]
    rfl

theorem negative_layer_mem_span (weight : I→ℤ) (S T : Set (Matrix I I K))
    (hS : ∀M∈S,Supported (fun i=> -weight i) (fun w=>w+1) M)
    (hT : ∀M∈T,Supported weight (fun w=>w+1) M)
    (h f e M : Matrix I I K) (hh : h.IsDiag)
    (hf : f∈LieSubalgebra.lieSpan K (Matrix I I K) S)
    (he : e∈LieSubalgebra.lieSpan K (Matrix I I K) T)
    (hsum : h+f+e=M)
    (hM : Supported (fun i=> -weight i) (fun w=>w+1) M) :
    M∈Submodule.span K S := by
  have hf' := firstPart_mem_span (fun i=> -weight i) S hS hf
  have he' := (positive_and_firstPart_mem_span weight T hT he).1
  have heq := congrArg (firstPart (fun i=> -weight i)) hsum
  rw [map_add,map_add,firstPart_diagonal_zero _ h hh,
    firstPart_opposite_zero weight e he',zero_add,add_zero,
    firstPart_eq_of_supported _ M hM] at heq
  rw [←heq]
  exact hf'

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieTriangularLayer
