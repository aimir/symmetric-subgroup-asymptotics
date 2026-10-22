import SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieFirstLayer
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-! Weak height support is preserved by actual Lie generation. A
homogeneous matrix in a triangular decomposition vanishes if its literal
lattice degree has both positive and negative coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieMixedDegree
open CFSGGradedMatrixSupport
variable {I J K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

def Nondecreasing (weight : I→ℤ) (M : Matrix I I K) : Prop :=
  ∀i j,weight i<weight j→M i j=0

omit [DecidableEq I] in
theorem nondecreasing_mul (weight : I→ℤ) (M N : Matrix I I K)
    (hM : Nondecreasing weight M) (hN : Nondecreasing weight N) :
    Nondecreasing weight (M*N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : weight i<weight k
  · rw [hM i k hik,zero_mul]
  · have hkj : weight k<weight j := by omega
    rw [hN k j hkj,mul_zero]

theorem nondecreasing_lieSpan (weight : I→ℤ) (S : Set (Matrix I I K))
    (hS : ∀M∈S,Nondecreasing weight M)
    {M : Matrix I I K} (hM : M∈LieSubalgebra.lieSpan K (Matrix I I K) S) :
    Nondecreasing weight M := by
  induction hM using LieSubalgebra.lieSpan_induction with
  | mem M hM=>exact hS M hM
  | zero=>intro i j hij;rfl
  | add M N _ _ hm hn=>
    intro i j hij
    rw [Matrix.add_apply,hm i j hij,hn i j hij,zero_add]
  | smul a M _ hm=>
    intro i j hij
    rw [Matrix.smul_apply,hm i j hij,smul_zero]
  | lie M N _ _ hm hn=>
    intro i j hij
    rw [Ring.lie_def,Matrix.sub_apply,
      nondecreasing_mul weight M N hm hn i j hij,
      nondecreasing_mul weight N M hn hm i j hij,sub_self]

omit [Fintype I] [DecidableEq I] in
theorem coordinate_nondecreasing_of_supported (weight : I→J→ℤ) (d : J→ℤ)
    (M : Matrix I I K) (hM : Supported weight (fun v=>v+d) M)
    (t : J) (hd : 0≤d t) : Nondecreasing (fun i=>weight i t) M := by
  intro i j hij
  apply hM i j
  intro he
  have ht := congrFun he t
  change weight i t=weight j t+d t at ht
  change weight i t<weight j t at hij
  omega

theorem mixed_degree_zero (weight : I→J→ℤ) (d : J→ℤ)
    (H F E M : Matrix I I K) (a b : J) (hH : H.IsDiag)
    (hF : Nondecreasing (fun i=> -(weight i a)) F)
    (hE : Nondecreasing (fun i=>weight i b) E)
    (hsum : H+F+E=M) (hM : Supported weight (fun v=>v+d) M)
    (ha : 0<d a) (hb : d b<0) : M=0 := by
  apply Matrix.ext
  intro i j
  by_cases heq : weight i=weight j+d
  · have hva := congrFun heq a
    have hvb := congrFun heq b
    change weight i a=weight j a+d a at hva
    change weight i b=weight j b+d b at hvb
    have hij : i≠j := by intro h;subst j;omega
    have hf : -weight i a< -weight j a := by omega
    have he : weight i b<weight j b := by omega
    rw [←hsum,Matrix.add_apply,Matrix.add_apply,hH hij,hF i j hf,hE i j he]
    simp only [zero_add,Matrix.zero_apply]
  · rw [hM i j heq]
    rfl

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieMixedDegree
