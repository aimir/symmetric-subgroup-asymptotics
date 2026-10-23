import SymmetricSubgroupAsymptotics.CFSGLinearMapImageOperators
import SymmetricSubgroupAsymptotics.CFSGQuadraticTripleProduct

/-! A literal cubic product on a common image. Quadratic identities
and mixed cancellations need hold only after the fixed map F. The
operator algebra used in the proof is End (range F), so no source
faithfulness or cancellation on the surrounding space is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinearMapImageTripleProduct
open CFSGLinearMapImageOperators
variable {K S V : Type*} [CommRing K]
    [AddCommGroup S] [Module K S] [AddCommGroup V] [Module K V]

theorem mapped_product_three (F : S →ₗ[K] V) (P Q R : Fin 3→Module.End K S)
    (T U : Fin 3→Module.End K V)
    (hP : ∀ i x, F (P i x)=T i (F x)) (hQ : ∀ i x, F (Q i x)=U i (F x))
    (hPQ : ∀ i j : Fin 3, i≠j→∀ x, F (P i (Q j x))=0)
    (hQP : ∀ i j : Fin 3, i≠j→∀ x, F (Q i (P j x))=0)
    (hQQ : ∀ i j : Fin 3, i≠j→∀ x, F (Q i (Q j x))=0)
    (t : K) (hR : ∀ i x, F (R i x)=F x+t • F (P i x)+t^2 • F (Q i x)) (x : S) :
    F (R 0 (R 1 (R 2 x)))=
      F x+t • (F (P 0 x)+F (P 1 x)+F (P 2 x))+
      t^2 • (F (Q 0 x)+F (Q 1 x)+F (Q 2 x)+
        F (P 0 (P 1 x))+F (P 0 (P 2 x))+F (P 1 (P 2 x)))+
      t^3 • F (P 0 (P 1 (P 2 x))) := by
  let E : Fin 3→Module.End K F.range:=fun i=>rangeOperator F (P i) (T i) (hP i)
  let D : Fin 3→Module.End K F.range:=fun i=>rangeOperator F (Q i) (U i) (hQ i)
  let q : S→ₗ[K]F.range:=F.rangeRestrict
  have he (i : Fin 3) (y : S) : E i (q y)=q (P i y) :=
    rangeOperator_rangeRestrict F (P i) (T i) (hP i) y
  have hd (i : Fin 3) (y : S) : D i (q y)=q (Q i y) :=
    rangeOperator_rangeRestrict F (Q i) (U i) (hQ i) y
  have hpq (i j : Fin 3) (hij : i≠j) : E i*D j=0 :=
    rangeOperator_mul_eq_zero F (P i) (Q j) (T i) (U j) (hP i) (hQ j) (hPQ i j hij)
  have hqp (i j : Fin 3) (hij : i≠j) : D i*E j=0 :=
    rangeOperator_mul_eq_zero F (Q i) (P j) (U i) (T j) (hQ i) (hP j) (hQP i j hij)
  have hqq (i j : Fin 3) (hij : i≠j) : D i*D j=0 :=
    rangeOperator_mul_eq_zero F (Q i) (Q j) (U i) (U j) (hQ i) (hQ j) (hQQ i j hij)
  have hr (i : Fin 3) (y : S) :
      q (R i y)=CFSGQuadraticTripleProduct.value (E i) (D i) t (q y) := by
    apply Subtype.ext
    change F (R i y)=F y+t • T i (F y)+t^2 • U i (F y)
    rw [hR,←hP,←hQ]
  have hv := CFSGQuadraticTripleProduct.product_three (E 0) (E 1) (E 2)
    (D 0) (D 1) (D 2) t
    (hpq 0 1 (by decide)) (hqp 0 1 (by decide)) (hqq 0 1 (by decide))
    (hpq 0 2 (by decide)) (hpq 1 2 (by decide)) (hqp 0 2 (by decide))
    (hqp 1 2 (by decide)) (hqq 0 2 (by decide)) (hqq 1 2 (by decide))
  have hx := congrArg (fun f : Module.End K F.range=>f (q x)) hv
  dsimp only at hx
  have hl : q (R 0 (R 1 (R 2 x)))=
      (CFSGQuadraticTripleProduct.value (E 0) (D 0) t*
        CFSGQuadraticTripleProduct.value (E 1) (D 1) t*
        CFSGQuadraticTripleProduct.value (E 2) (D 2) t) (q x) := by
    rw [hr, hr, hr]
    rfl
  rw [←hl] at hx
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply, he, hd] at hx
  exact congrArg Subtype.val hx

end SymmetricSubgroupAsymptotics.CFSGLinearMapImageTripleProduct
