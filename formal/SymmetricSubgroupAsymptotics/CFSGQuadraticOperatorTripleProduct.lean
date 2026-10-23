import SymmetricSubgroupAsymptotics.CFSGQuadraticTripleProduct

/-! The rational quadratic operator values of three commuting roots
retain the literal cubic composition. Mixed three-letter vanishing
kills every cross-second term. There is no division by three or six. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticOperatorTripleProduct
variable {R : Type*} [Ring R] [Algebra ℚ R]

theorem product_three (T : Fin 3→R)
    (hcomm : ∀i j : Fin 3,i≠j→Commute (T i) (T j))
    (hmixed : ∀i j : Fin 3,i≠j→(T i)^2*T j=0) (t : ℚ) :
    CFSGQuadraticTripleProduct.value (T 0) ((1/2:ℚ) • (T 0)^2) t*
      CFSGQuadraticTripleProduct.value (T 1) ((1/2:ℚ) • (T 1)^2) t*
      CFSGQuadraticTripleProduct.value (T 2) ((1/2:ℚ) • (T 2)^2) t=
      1+t • (T 0+T 1+T 2)+
        t^2 • ((1/2:ℚ) • (T 0)^2+(1/2:ℚ) • (T 1)^2+(1/2:ℚ) • (T 2)^2+
          T 0*T 1+T 0*T 2+T 1*T 2)+t^3 • (T 0*T 1*T 2) := by
  have hTS (i j : Fin 3) (hij : i≠j) : T i*((1/2:ℚ) • (T j)^2)=0 := by
    rw [mul_smul_comm,((hcomm i j hij).pow_right 2).eq,hmixed j i (Ne.symm hij),smul_zero]
  have hST (i j : Fin 3) (hij : i≠j) : ((1/2:ℚ) • (T i)^2)*T j=0 := by
    rw [smul_mul_assoc,hmixed i j hij,smul_zero]
  have hSS (i j : Fin 3) (hij : i≠j) :
      ((1/2:ℚ) • (T i)^2)*((1/2:ℚ) • (T j)^2)=0 := by
    have hh : (T i)^2*(T j)^2=0 := by
      calc
        _=((T i)^2*T j)*T j := by rw [pow_two (T j),mul_assoc]
        _=0 := by rw [hmixed i j hij,zero_mul]
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,hh,smul_zero]
  exact CFSGQuadraticTripleProduct.product_three (T 0) (T 1) (T 2)
    ((1/2:ℚ) • (T 0)^2) ((1/2:ℚ) • (T 1)^2) ((1/2:ℚ) • (T 2)^2) t
    (hTS 0 1 (by decide)) (hST 0 1 (by decide)) (hSS 0 1 (by decide))
    (hTS 0 2 (by decide)) (hTS 1 2 (by decide)) (hST 0 2 (by decide))
    (hST 1 2 (by decide)) (hSS 0 2 (by decide)) (hSS 1 2 (by decide))

end SymmetricSubgroupAsymptotics.CFSGQuadraticOperatorTripleProduct
