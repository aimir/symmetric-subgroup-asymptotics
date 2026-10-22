import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups

/-! A quadratic root word remembers its two actual homogeneous
coefficients. Conjugating them transports the degrees, without assuming
that a root space is one-dimensional or choosing a new root operator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedQuadraticUnit
open CFSGGradedMatrixSupport CFSGGradedMatrixSubgroups
variable {I K L : Type*} [Fintype I] [DecidableEq I] [CommRing K] [AddCommGroup L]

def QuadraticGrade (weight : I→L) (d : L) (u : (Matrix I I K)ˣ) : Prop :=
  ∃E D : Matrix I I K,(u : Matrix I I K)=1+E+D ∧
    Supported weight (fun w=>w+d) E ∧ Supported weight (fun w=>w+(d+d)) D

theorem supported_smul (weight : I→L) (f : L→L) (M : Matrix I I K)
    (hM : Supported weight f M) (t : K) : Supported weight f (t • M) := by
  intro i j hij
  rw [Matrix.smul_apply,hM i j hij,smul_zero]

theorem conjugate (weight : I→L) (d : L) (e : L≃+L)
    (p u : (Matrix I I K)ˣ)
    (hP : Supported weight e (p : Matrix I I K))
    (hQ : Supported weight e.symm (↑(p⁻¹) : Matrix I I K))
    (hu : QuadraticGrade weight d u) : QuadraticGrade weight (e d) (p*u*p⁻¹) := by
  obtain ⟨E,D,he,hE,hD⟩ := hu
  refine ⟨(p : Matrix I I K)*E*(↑(p⁻¹) : Matrix I I K),
    (p : Matrix I I K)*D*(↑(p⁻¹) : Matrix I I K),?_,?_,?_⟩
  · change (p : Matrix I I K)*(u : Matrix I I K)*(↑(p⁻¹) : Matrix I I K)=_
    rw [he,mul_add,mul_add,add_mul,add_mul,mul_one,Units.mul_inv]
  · exact supported_conjugation weight e d _ _ _ hP hE hQ
  · have hh := supported_conjugation weight e (d+d) _ _ _ hP hD hQ
    simpa only [map_add] using hh

theorem support_apply_height (weight : I→L) (d : L) (H : L→+ℤ)
    (M : Matrix I I K) (hM : Supported weight (fun w=>w+d) M) :
    Supported (H∘weight) (fun w=>w+H d) M := by
  intro i j hij
  apply hM i j
  intro he
  apply hij
  change H (weight i)=H (weight j)+H d
  rw [he,map_add]

theorem preserves_of_height_zero (weight : I→L) (d : L) (H : L→+ℤ)
    (u : (Matrix I I K)ˣ) (hu : QuadraticGrade weight d u) (hd : H d=0) :
    Supported (H∘weight) id (u : Matrix I I K) := by
  obtain ⟨E,D,he,hE,hD⟩ := hu
  have hEh : Supported (H∘weight) id E := by
    simpa only [hd,add_zero] using support_apply_height weight d H E hE
  have hDh : Supported (H∘weight) id D := by
    simpa only [map_add,hd,zero_add,add_zero] using support_apply_height weight (d+d) H D hD
  rw [he]
  exact supported_add (supported_add (supported_one (H∘weight)) hEh) hDh

theorem strict_of_height_positive (weight : I→L) (d : L) (H : L→+ℤ)
    (u : (Matrix I I K)ˣ) (hu : QuadraticGrade weight d u) (hd : 0<H d) :
    ∀i j,H (weight i)≤H (weight j)→(u : Matrix I I K) i j=(1 : Matrix I I K) i j := by
  obtain ⟨E,D,he,hE,hD⟩ := hu
  intro i j hij
  have hEz : E i j=0 := by
    apply hE i j
    intro hh
    have ht := congrArg H hh
    rw [map_add] at ht
    omega
  have hDz : D i j=0 := by
    apply hD i j
    intro hh
    have ht := congrArg H hh
    rw [map_add,map_add] at ht
    omega
  rw [he,Matrix.add_apply,Matrix.add_apply,hEz,hDz,add_zero,add_zero]

end SymmetricSubgroupAsymptotics.CFSGGradedQuadraticUnit
