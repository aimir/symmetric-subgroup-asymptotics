import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! A hyperbolic-pair chart bounds the zero cone without an order
formula for an orthogonal group. The residual function is arbitrary:
if the first coordinate is nonzero the last is determined, and if it
vanishes the other two coordinates suffice. This is the vector-count
foundation for the split odd-dimensional singular-point bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSplitOddSingularPointCardinality

def zeroCone {K W : Type*} [Field K] (Q : W→K) :=
  {v : K×W×K // v.1*v.2.2+Q v.2.1=0}

theorem zeroCone_card_le {K W : Type*} [Field K] [Finite K] [Finite W] (Q : W→K) :
    Nat.card (zeroCone Q)≤2*Nat.card K*Nat.card W := by
  classical
  let encode : zeroCone Q→(K×W)⊕(W×K) := fun x=>
    if x.val.1=0 then Sum.inr (x.val.2.1,x.val.2.2) else Sum.inl (x.val.1,x.val.2.1)
  have hinj : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    by_cases hx : x.val.1=0
    · by_cases hy : y.val.1=0
      · have hp : (x.val.2.1,x.val.2.2)=(y.val.2.1,y.val.2.2) := by
          simpa only [encode,if_pos hx,if_pos hy,Sum.inr.injEq] using he
        exact Prod.ext (hx.trans hy.symm) hp
      · simp only [encode,if_pos hx,if_neg hy,Sum.inr_ne_inl] at he
    · by_cases hy : y.val.1=0
      · simp only [encode,if_neg hx,if_pos hy,Sum.inl_ne_inr] at he
      · have hp : (x.val.1,x.val.2.1)=(y.val.1,y.val.2.1) := by
          simpa only [encode,if_neg hx,if_neg hy,Sum.inl.injEq] using he
        have ha := congrArg Prod.fst hp
        have hw := congrArg Prod.snd hp
        have hb : x.val.2.2=y.val.2.2 := by
          apply mul_left_cancel₀ hx
          calc
            x.val.1*x.val.2.2= -Q x.val.2.1 := eq_neg_of_add_eq_zero_left x.property
            _= -Q y.val.2.1 := congrArg (fun w=>-Q w) hw
            _=y.val.1*y.val.2.2 := (eq_neg_of_add_eq_zero_left y.property).symm
            _=x.val.1*y.val.2.2 := by rw [ha]
        exact Prod.ext ha (Prod.ext hw hb)
  calc
    _≤Nat.card ((K×W)⊕(W×K)) := Nat.card_le_card_of_injective encode hinj
    _=Nat.card K*Nat.card W+Nat.card W*Nat.card K := by
      rw [Nat.card_sum,Nat.card_prod,Nat.card_prod]
    _=2*Nat.card K*Nat.card W := by ring

theorem point_card_lt_three_mul_pow (q n M : ℕ) (hq : 3≤q)
    (hcone : M*(q-1)+1≤2*q*q^n) : M<3*q^n := by
  have hbound : 2*q*q^n≤(3*q^n)*(q-1) := by
    have hsub : q-1+1=q := by omega
    have hscaled : (q-1+1)*q^n=q*q^n := congrArg (fun a=>a*q^n) hsub
    have hqscaled : 3*q^n≤q*q^n := Nat.mul_le_mul_right _ hq
    nlinarith
  apply (Nat.mul_lt_mul_right (by omega : 0<q-1)).mp
  exact (by omega : M*(q-1)<2*q*q^n).trans_le hbound

theorem square_lt_twelfth_pow (q M : ℕ) (hq : 3≤q) (hM : M<3*q^5) : M^2<q^12 := by
  have hq2 : 9≤q^2 := by nlinarith
  have hp : M^2<(3*q^5)^2 := Nat.pow_lt_pow_left hM (by decide)
  calc
    M^2<(3*q^5)^2 := hp
    _=9*q^10 := by ring
    _≤q^2*q^10 := Nat.mul_le_mul_right _ hq2
    _=q^12 := by ring

end SymmetricSubgroupAsymptotics.CFSGSplitOddSingularPointCardinality
