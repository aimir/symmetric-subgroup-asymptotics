import SymmetricSubgroupAsymptotics.CFSGSuzukiNorm
import SymmetricSubgroupAsymptotics.CFSGSuzukiZeroFirstBruhat

/-! The general Suzuki rank-one Bruhat array identity. Every term is an
original unipotent array, the explicitly normalized original torus, or
the original reversing matrix; no BN-pair or group-order premise enters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiBruhat
open CFSGSuzukiNorm CFSGSuzukiTorus CFSGSuzukiUnipotent CFSGSuzukiFieldParameters
variable {K : Type*} [Field K] [CharP K 2]

theorem general_bruhat_array (t : K →+* K) (ht : ∀ x,t (t x)=x^2)
    (a b : K) (hN : twistedNorm t a b≠0) :
    reversingArray*twistedArray t a b*reversingArray=
      twistedArray t (b/twistedNorm t a b) (a/twistedNorm t a b)*
        diagonalTorus t (twistedNorm t a b)*reversingArray*
        twistedArray t ((a*t a+b)/twistedNorm t a b) (b/t (twistedNorm t a b)) := by
  have hTN : t (twistedNorm t a b)≠0 := by
    intro he
    apply hN
    apply t.injective
    simpa only [map_zero] using he
  ext i j
  simp only [mul_reversingArray_apply,reversingArray_mul_apply]
  rw [Matrix.mul_apply]
  simp only [mul_reversingArray_apply,diagonalTorus,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [twistedArray,Fin.sum_univ_succ,map_div₀,map_mul,map_add,ht,Fin.rev] <;>
    field_simp [hN,hTN] <;>
    simp only [twistedNorm,map_add,map_mul,map_pow,ht] <;>
    ring_nf <;> simp

theorem general_bruhat (m : ℕ) (a b : Field m) (hab : a≠0 ∨ b≠0) :
    weylElement m*unipotentElement m a b*weylElement m=
      unipotentElement m (b/suzukiNorm m a b) (a/suzukiNorm m a b)*
        normalizedTorusElement m (Units.mk0 (suzukiNorm m a b) (suzukiNorm_ne_zero m hab))*
        weylElement m*
        unipotentElement m ((a*theta m a+b)/suzukiNorm m a b)
          (b/theta m (suzukiNorm m a b)) := by
  apply Units.ext
  change CFSG.Models.SuzukiConstruction.weyl m*
      CFSG.Models.SuzukiConstruction.unipotent m a b*CFSG.Models.SuzukiConstruction.weyl m=
    CFSG.Models.SuzukiConstruction.unipotent m (b/suzukiNorm m a b) (a/suzukiNorm m a b)*
      (normalizedTorusElement m (Units.mk0 (suzukiNorm m a b) (suzukiNorm_ne_zero m hab)) :
        CFSG.Models.SuzukiConstruction.Mat m)*CFSG.Models.SuzukiConstruction.weyl m*
      CFSG.Models.SuzukiConstruction.unipotent m ((a*theta m a+b)/suzukiNorm m a b)
        (b/theta m (suzukiNorm m a b))
  rw [normalizedTorusElement_coe]
  simp only [unipotent_eq_twistedArray]
  exact general_bruhat_array (theta m) (theta_twice m) a b (suzukiNorm_ne_zero m hab)

/-- Exact parameter normal form for the conjugate of every original U
element, including its identity case. -/
theorem weyl_unipotent_weyl_normal_form (m : ℕ) (a b : Field m) :
    weylElement m*unipotentElement m a b*weylElement m=1 ∨
      ∃ x y : Field m,∃ c : (Field m)ˣ,∃ z w : Field m,
        weylElement m*unipotentElement m a b*weylElement m=
          unipotentElement m x y*normalizedTorusElement m c*weylElement m*unipotentElement m z w := by
  by_cases hh : a=0 ∧ b=0
  · left
    rw [hh.1,hh.2,unipotentElement_zero,mul_one,weylElement_square]
  · have hab : a≠0 ∨ b≠0 := by tauto
    right
    exact ⟨_,_,_,_,_,general_bruhat m a b hab⟩

/-- The big cell's original first-row last-column entry is its nonzero
torus parameter. This is the exact exclusion used with U's fixed line. -/
theorem big_cell_entry_zero_three (m : ℕ) (a b : Field m) (c : (Field m)ˣ) (x y : Field m) :
    ((unipotentElement m a b*normalizedTorusElement m c*weylElement m*unipotentElement m x y :
      CFSGSuzukiTorus.Ambient m) : CFSG.Models.SuzukiConstruction.Mat m) 0 3=(c : Field m) := by
  simp only [Units.val_mul,unipotentElement_coe,normalizedTorusElement_coe,
    weylElement_coe,unipotent_eq_twistedArray]
  change ((twistedArray (theta m) a b*diagonalTorus (theta m) (c : Field m)*
    reversingArray*twistedArray (theta m) x y) :
      CFSG.Models.SuzukiConstruction.Mat m) 0 3=(c : Field m)
  rw [Matrix.mul_apply]
  simp only [mul_reversingArray_apply,diagonalTorus,Matrix.mul_diagonal]
  simp [twistedArray,Fin.sum_univ_succ,Fin.rev]

end SymmetricSubgroupAsymptotics.CFSGSuzukiBruhat
