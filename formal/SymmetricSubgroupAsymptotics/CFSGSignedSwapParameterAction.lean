import SymmetricSubgroupAsymptotics.CFSGAdditiveParameterConjugation

/-! A signed coordinate swap conjugates a forward elementary row into
the reverse row, after an explicit invertible scalar change. The signs
on the other coordinates are unrestricted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSignedSwapParameterAction
open CFSGAdditiveParameterConjugation CFSGTypeAElementaryMatrices
variable {J K : Type*} [Fintype J] [DecidableEq J] [Field K]

def signedSwap (p q:J) (d:J→Kˣ) : (J→K)≃ₗ[K](J→K) where
  toFun v k := (d (Equiv.swap p q k):K)*v (Equiv.swap p q k)
  invFun v k := (d k:K)⁻¹*v (Equiv.swap p q k)
  left_inv v := by
    ext k
    simp only [Equiv.swap_apply_self,←mul_assoc,inv_mul_cancel₀ (Units.ne_zero _),one_mul]
  right_inv v := by
    ext k
    simp only [Equiv.swap_apply_self,←mul_assoc,mul_inv_cancel₀ (Units.ne_zero _),one_mul]
  map_add' v w := by
    ext k
    exact mul_add _ _ _
  map_smul' a v := by
    ext k
    change (d (Equiv.swap p q k):K)*(a*v (Equiv.swap p q k))=
      a*((d (Equiv.swap p q k):K)*v (Equiv.swap p q k))
    ring

theorem signedSwap_apply (p q:J)(d:J→Kˣ)(v:J→K)(k:J) :
    signedSwap p q d v k=(d (Equiv.swap p q k):K)*v (Equiv.swap p q k) := rfl

theorem signedSwap_symm_apply (p q:J)(d:J→Kˣ)(v:J→K)(k:J) :
    (signedSwap p q d).symm v k=(d k:K)⁻¹*v (Equiv.swap p q k) := rfl

theorem signedSwap_single (p q:J)(d:J→Kˣ)(i:J)(a:K) :
    signedSwap p q d (Pi.single i a)=Pi.single (Equiv.swap p q i) ((d i:K)*a) := by
  ext k
  rw [signedSwap_apply]
  by_cases hk:k=Equiv.swap p q i
  · subst k
    rw [Equiv.swap_apply_self,Pi.single_eq_same,Pi.single_eq_same]
  · have hki : Equiv.swap p q k≠i := by
      intro he
      apply hk
      calc
        k=Equiv.swap p q (Equiv.swap p q k) := (Equiv.swap_apply_self p q k).symm
        _=Equiv.swap p q i := congrArg (Equiv.swap p q) he
    rw [Pi.single_eq_of_ne hki,Pi.single_eq_of_ne hk,mul_zero]

theorem conjugate_forward (p q:J)(hpq:p≠q)(d:J→Kˣ)(a:K)(v:J→K) :
    signedSwap p q d
      ((elementary hpq.symm ((d p:K)*(d q:K)⁻¹*a)).toLin'
        ((signedSwap p q d).symm v))=(elementary hpq a).toLin' v := by
  rw [elementary_apply,map_add,LinearEquiv.apply_symm_apply,signedSwap_single,
    Equiv.swap_apply_right,elementary_apply,signedSwap_symm_apply,Equiv.swap_apply_left]
  have hcoef : (d q:K)*(((d p:K)*(d q:K)⁻¹*a)*((d p:K)⁻¹*v q))=a*v q := by
    field_simp [Units.ne_zero (d p),Units.ne_zero (d q)]
    <;> ring
  rw [hcoef]

end SymmetricSubgroupAsymptotics.CFSGSignedSwapParameterAction
