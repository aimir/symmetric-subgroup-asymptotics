import SymmetricSubgroupAsymptotics.CFSGLinearMapImageTripleProduct

/-! Independent parameters in the literal cubic image formula. Scaling
the integral first and second coefficients by a_i and a_i^2 gives the
three-parameter identity without changing any characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinearMapImageParameterizedTripleProduct
variable {K S V : Type*} [CommRing K]
    [AddCommGroup S] [Module K S] [AddCommGroup V] [Module K V]

theorem mapped_product_three (F : S →ₗ[K] V) (P Q R : Fin 3→Module.End K S)
    (T U : Fin 3→Module.End K V)
    (hP : ∀ i x, F (P i x)=T i (F x)) (hQ : ∀ i x, F (Q i x)=U i (F x))
    (hPQ : ∀ i j : Fin 3, i≠j→∀ x, F (P i (Q j x))=0)
    (hQP : ∀ i j : Fin 3, i≠j→∀ x, F (Q i (P j x))=0)
    (hQQ : ∀ i j : Fin 3, i≠j→∀ x, F (Q i (Q j x))=0)
    (a : Fin 3→K)
    (hR : ∀ i x, F (R i x)=F x+a i • F (P i x)+(a i)^2 • F (Q i x)) (x : S) :
    F (R 0 (R 1 (R 2 x)))=
      F x+(a 0 • F (P 0 x)+a 1 • F (P 1 x)+a 2 • F (P 2 x))+
      ((a 0)^2 • F (Q 0 x)+(a 1)^2 • F (Q 1 x)+(a 2)^2 • F (Q 2 x)+
        (a 0*a 1) • F (P 0 (P 1 x))+(a 0*a 2) • F (P 0 (P 2 x))+
        (a 1*a 2) • F (P 1 (P 2 x)))+
      (a 0*a 1*a 2) • F (P 0 (P 1 (P 2 x))) := by
  let P' : Fin 3→Module.End K S:=fun i=>a i • P i
  let Q' : Fin 3→Module.End K S:=fun i=>(a i)^2 • Q i
  let T' : Fin 3→Module.End K V:=fun i=>a i • T i
  let U' : Fin 3→Module.End K V:=fun i=>(a i)^2 • U i
  have hp (i : Fin 3) (y : S) : F (P' i y)=T' i (F y) := by
    simp only [P',T',LinearMap.smul_apply,map_smul,hP]
  have hq (i : Fin 3) (y : S) : F (Q' i y)=U' i (F y) := by
    simp only [Q',U',LinearMap.smul_apply,map_smul,hQ]
  have hpq (i j : Fin 3) (hij : i≠j) (y : S) : F (P' i (Q' j y))=0 := by
    simp only [P',Q',LinearMap.smul_apply,map_smul,hPQ i j hij,smul_zero]
  have hqp (i j : Fin 3) (hij : i≠j) (y : S) : F (Q' i (P' j y))=0 := by
    simp only [P',Q',LinearMap.smul_apply,map_smul,hQP i j hij,smul_zero]
  have hqq (i j : Fin 3) (hij : i≠j) (y : S) : F (Q' i (Q' j y))=0 := by
    simp only [Q',LinearMap.smul_apply,map_smul,hQQ i j hij,smul_zero]
  have hr (i : Fin 3) (y : S) :
      F (R i y)=F y+(1:K) • F (P' i y)+(1:K)^2 • F (Q' i y) := by
    simpa only [P',Q',LinearMap.smul_apply,map_smul,one_pow,one_smul] using hR i y
  have hh:=CFSGLinearMapImageTripleProduct.mapped_product_three F P' Q' R T' U'
    hp hq hpq hqp hqq (1:K) hr x
  simpa only [P',Q',LinearMap.smul_apply,map_smul,smul_smul,one_pow,one_smul,one_mul,mul_comm,mul_left_comm,mul_assoc] using hh

end SymmetricSubgroupAsymptotics.CFSGLinearMapImageParameterizedTripleProduct
