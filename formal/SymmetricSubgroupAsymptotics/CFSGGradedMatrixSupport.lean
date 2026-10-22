import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Matrix support relative to a literal grading. The multiplication lemma
tracks arbitrary maps of degrees, so it also applies to root reflections.
No eigenvalue separation in the coefficient field is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport
variable {I R W : Type*} [Fintype I] [DecidableEq I] [Semiring R]

def Supported (weight : I→W) (f : W→W) (M : Matrix I I R) : Prop :=
  ∀ i j,weight i≠f (weight j)→M i j=0

theorem supported_one (weight : I→W) :
    Supported weight id (1 : Matrix I I R) := by
  intro i j hij
  have hne : i≠j := by intro h;subst j;exact hij rfl
  simp only [Matrix.one_apply,if_neg hne]

theorem supported_add {weight : I→W} {f : W→W} {M N : Matrix I I R}
    (hM : Supported weight f M) (hN : Supported weight f N) :
    Supported weight f (M+N) := by
  intro i j hij
  rw [Matrix.add_apply,hM i j hij,hN i j hij,zero_add]

theorem supported_mul {weight : I→W} {f g : W→W} {M N : Matrix I I R}
    (hM : Supported weight f M) (hN : Supported weight g N) :
    Supported weight (f∘g) (M*N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : weight i=f (weight k)
  · have hkj : weight k≠g (weight j) := by
      intro hk
      exact hij (hik.trans (congrArg f hk))
    rw [hN k j hkj,mul_zero]
  · rw [hM i k hik,zero_mul]

theorem supported_congr {weight : I→W} {f g : W→W} {M : Matrix I I R}
    (hM : Supported weight f M) (hfg : ∀ w,f w=g w) :
    Supported weight g M := by
  intro i j hij
  apply hM i j
  simpa only [hfg] using hij

theorem supported_conjugation {L : Type*} [AddCommGroup L]
    (weight : I→L) (e : L≃+L) (d : L) (P M Q : Matrix I I R)
    (hP : Supported weight e P)
    (hM : Supported weight (fun w=>w+d) M)
    (hQ : Supported weight e.symm Q) :
    Supported weight (fun w=>w+e d) (P*M*Q) := by
  apply supported_congr (supported_mul (supported_mul hP hM) hQ)
  intro w
  simp only [Function.comp_apply,map_add,AddEquiv.apply_symm_apply]

theorem eq_one_of_preserves_of_nonincreasing {weight : I→ℤ} {M : Matrix I I R}
    (hM : Supported weight id M)
    (hstrict : ∀ i j,weight i≤weight j→M i j=(1 : Matrix I I R) i j) :
    M=1 := by
  apply Matrix.ext
  intro i j
  by_cases hij : weight i=weight j
  · exact hstrict i j (le_of_eq hij)
  · have hne : i≠j := by intro h;subst j;exact hij rfl
    rw [hM i j hij,Matrix.one_apply,if_neg hne]

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport
