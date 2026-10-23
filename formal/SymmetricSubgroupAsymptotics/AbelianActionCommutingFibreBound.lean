import SymmetricSubgroupAsymptotics.FrobeniusAbelianMotion
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Uniform commuting-fibre bounds from actual fixed-point capacities.
The complement is arbitrary. Only the kernel is abelian, and neither
freeness of the action nor a separate conjugacy estimate is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AbelianActionCommutingFibreBound
open FrobeniusAbelianMotion

theorem hom_fibre_card_le_ker {G Q : Type*} [Group G] [Group Q] [Finite G]
    (f : G →* Q) (y : Q) : Nat.card {g : G // f g=y} ≤ Nat.card f.ker := by
  by_cases hn : Nonempty {g : G // f g=y}
  · let b := Classical.choice hn
    let delta : {g : G // f g=y} → f.ker := fun x => ⟨x.val*b.val⁻¹, by
      change f (x.val*b.val⁻¹)=1
      rw [map_mul,map_inv,x.property,b.property,mul_inv_cancel]⟩
    apply Nat.card_le_card_of_injective delta
    intro x z he
    apply Subtype.ext
    exact mul_right_cancel (congrArg Subtype.val he)
  · letI : IsEmpty {g : G // f g=y} := not_nonempty_iff.mp hn
    have hz : Nat.card {g : G // f g=y}=0 := Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hz]
    exact Nat.zero_le _

variable {N H : Type*} [CommGroup N] [Group H] (phi : H →* MulAut N)

abbrev Fibre (h k : H) :=
  {p : N×N // Commute (⟨p.1,h⟩ : N ⋊[phi] H) (⟨p.2,k⟩ : N ⋊[phi] H)}

theorem motion_eq_of_commute (h k : H) (a b : N)
    (hc : Commute (⟨a,h⟩ : N ⋊[phi] H) (⟨b,k⟩ : N ⋊[phi] H)) :
    motion (phi h) b=motion (phi k) a := by
  have he : a*phi h b=b*phi k a := congrArg SemidirectProduct.left hc
  calc
    motion (phi h) b=(a*phi h b)*(b⁻¹*a⁻¹) := by
      change phi h b*b⁻¹=(a*phi h b)*(b⁻¹*a⁻¹)
      calc
        _=(a*a⁻¹)*(phi h b*b⁻¹) := by rw [mul_inv_cancel,one_mul]
        _=_ := by ac_rfl
    _=(b*phi k a)*(b⁻¹*a⁻¹) := congrArg (fun z : N => z*(b⁻¹*a⁻¹)) he
    _=motion (phi k) a := by
      change (b*phi k a)*(b⁻¹*a⁻¹)=phi k a*a⁻¹
      calc
        _=(b*b⁻¹)*(phi k a*a⁻¹) := by ac_rfl
        _=_ := by rw [mul_inv_cancel,one_mul]

def swapEquiv (h k : H) : Fibre phi h k ≃ Fibre phi k h where
  toFun p := ⟨(p.val.2,p.val.1),p.property.symm⟩
  invFun p := ⟨(p.val.2,p.val.1),p.property.symm⟩
  left_inv _p := rfl
  right_inv _p := rfl

variable [Finite N]

theorem motion_kernel_card_le_fixed (h : H) :
    Nat.card (motion (phi h)).ker ≤ Nat.card {n : N // phi h n=n} := by
  let f : (motion (phi h)).ker → {n : N // phi h n=n} := fun x => ⟨x.val,by
    have hx : phi h x.val*x.val⁻¹=1 := x.property
    exact mul_inv_eq_one.mp hx⟩
  apply Nat.card_le_card_of_injective f
  intro x y he
  apply Subtype.ext
  exact congrArg (fun z : {n : N // phi h n=n} => z.val) he

theorem fibre_card_le_left (h k : H) :
    Nat.card (Fibre phi h k) ≤ Nat.card N*Nat.card {n : N // phi h n=n} := by
  letI : Fintype N := Fintype.ofFinite _
  let T := (a : N) × {b : N // motion (phi h) b=motion (phi k) a}
  let f : Fibre phi h k → T := fun p =>
    ⟨p.val.1,⟨p.val.2,motion_eq_of_commute phi h k p.val.1 p.val.2 p.property⟩⟩
  let forget : T → N×N := fun t => (t.1,t.2.val)
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg forget he)
  calc
    Nat.card (Fibre phi h k) ≤ Nat.card T := Nat.card_le_card_of_injective f hf
    _ = ∑ a : N, Nat.card {b : N // motion (phi h) b=motion (phi k) a} := Nat.card_sigma
    _ ≤ ∑ _a : N, Nat.card (motion (phi h)).ker :=
      Finset.sum_le_sum (fun a _ => hom_fibre_card_le_ker (motion (phi h)) (motion (phi k) a))
    _ = Nat.card N*Nat.card (motion (phi h)).ker := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
    _ ≤ Nat.card N*Nat.card {n : N // phi h n=n} :=
      Nat.mul_le_mul_left _ (motion_kernel_card_le_fixed phi h)

theorem fibre_card_le_off_identity (c : ℕ)
    (hfixed : ∀ h : H, h≠1 → Nat.card {n : N // phi h n=n} ≤ c)
    (h k : H) (hpair : ¬ (h=1 ∧ k=1)) : Nat.card (Fibre phi h k) ≤ Nat.card N*c := by
  by_cases hh : h=1
  · have hk : k≠1 := fun hk => hpair ⟨hh,hk⟩
    rw [Nat.card_congr (swapEquiv phi h k)]
    exact (fibre_card_le_left phi k h).trans (Nat.mul_le_mul_left _ (hfixed k hk))
  · exact (fibre_card_le_left phi h k).trans (Nat.mul_le_mul_left _ (hfixed h hh))

end SymmetricSubgroupAsymptotics.AbelianActionCommutingFibreBound
