import SymmetricSubgroupAsymptotics.FrobeniusAbelianMotion
import Mathlib.GroupTheory.SemidirectProduct

/-! Every joint commuting fibre of an abelian-by-abelian Frobenius
semidirect product is counted. The identity fibre is N squared; every
other fibre is in actual bijection with N using the difference inverse. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FrobeniusAbelianCommutingFibres
open FrobeniusAbelianMotion

variable {N H : Type*} [CommGroup N] [CommGroup H] (φ : H →* MulAut N)

abbrev Fibre (h k : H) :=
  {p : N × N // Commute (⟨p.1,h⟩ : N ⋊[φ] H) (⟨p.2,k⟩ : N ⋊[φ] H)}

theorem commute_iff_motion (h k : H) (a b : N) :
    Commute (⟨a,h⟩ : N ⋊[φ] H) (⟨b,k⟩ : N ⋊[φ] H) ↔
      motion (φ h) b=motion (φ k) a := by
  constructor
  · intro hc
    have he : a*φ h b=b*φ k a := congrArg SemidirectProduct.left hc
    calc
      motion (φ h) b = (a*φ h b)*(b⁻¹*a⁻¹) := by
        change φ h b*b⁻¹=(a*φ h b)*(b⁻¹*a⁻¹)
        calc
          φ h b*b⁻¹ = (a*a⁻¹)*(φ h b*b⁻¹) := by rw [mul_inv_cancel,one_mul]
          _ = (a*φ h b)*(b⁻¹*a⁻¹) := by ac_rfl
      _ = (b*φ k a)*(b⁻¹*a⁻¹) := congrArg (fun z : N => z*(b⁻¹*a⁻¹)) he
      _ = motion (φ k) a := by
        change (b*φ k a)*(b⁻¹*a⁻¹)=φ k a*a⁻¹
        calc
          (b*φ k a)*(b⁻¹*a⁻¹) = (b*b⁻¹)*(φ k a*a⁻¹) := by ac_rfl
          _ = φ k a*a⁻¹ := by rw [mul_inv_cancel,one_mul]
  · intro he
    apply SemidirectProduct.ext
    · change a*φ h b=b*φ k a
      calc
        a*φ h b = motion (φ h) b*(a*b) := by
          change a*φ h b=(φ h b*b⁻¹)*(a*b)
          calc
            a*φ h b = (b⁻¹*b)*(a*φ h b) := by rw [inv_mul_cancel,one_mul]
            _ = (φ h b*b⁻¹)*(a*b) := by ac_rfl
        _ = motion (φ k) a*(a*b) := congrArg (fun z : N => z*(a*b)) he
        _ = b*φ k a := by
          change (φ k a*a⁻¹)*(a*b)=b*φ k a
          calc
            (φ k a*a⁻¹)*(a*b) = (a⁻¹*a)*(b*φ k a) := by ac_rfl
            _ = b*φ k a := by rw [inv_mul_cancel,one_mul]
    · exact mul_comm h k

def swapEquiv (h k : H) : Fibre φ h k ≃ Fibre φ k h where
  toFun p := ⟨(p.val.2,p.val.1),p.property.symm⟩
  invFun p := ⟨(p.val.2,p.val.1),p.property.symm⟩
  left_inv _p := rfl
  right_inv _p := rfl

def identityFibreEquiv : N × N ≃ Fibre φ 1 1 where
  toFun p := ⟨p,by apply (commute_iff_motion φ 1 1 _ _).mpr; simp [motion]⟩
  invFun p := p.val
  left_inv _p := rfl
  right_inv _p := rfl

variable [Finite N]
    (hfree : ∀ (h : H), h≠1 → ∀ n : N, φ h n=n → n=1)

def leftFibreEquiv (h k : H) (hh : h≠1) : N ≃ Fibre φ h k where
  toFun a := ⟨(a,(motionEquiv (φ h) (hfree h hh)).symm (motion (φ k) a)),by
    apply (commute_iff_motion φ h k _ _).mpr
    exact (motionEquiv (φ h) (hfree h hh)).apply_symm_apply _⟩
  invFun p := p.val.1
  left_inv a := rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply (motionEquiv (φ h) (hfree h hh)).injective
      rw [MulEquiv.apply_symm_apply]
      exact ((commute_iff_motion φ h k _ _).mp p.property).symm

include hfree in
theorem fibre_card (h k : H) :
    Nat.card (Fibre φ h k) = if h=1 ∧ k=1 then (Nat.card N)^2 else Nat.card N := by
  by_cases hh : h=1
  · subst h
    by_cases hk : k=1
    · subst k
      rw [if_pos ⟨rfl,rfl⟩,← Nat.card_congr (identityFibreEquiv φ),Nat.card_prod,pow_two]
    · rw [if_neg (by simp [hk])]
      exact (Nat.card_congr
        ((leftFibreEquiv φ hfree k 1 hk).trans (swapEquiv φ k 1))).symm
  · rw [if_neg (by simp [hh])]
    exact (Nat.card_congr (leftFibreEquiv φ hfree h k hh)).symm

end SymmetricSubgroupAsymptotics.FrobeniusAbelianCommutingFibres
