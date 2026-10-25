import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Ring

/-! Adding one coordinate whose norm has one zero preimage and q+1
preimages at every nonzero value gives an exact fibre recurrence. The
old coordinate function is arbitrary. No isometry group is counted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteNormSumFibreRecurrence

variable {F E K : Type*} [AddCommGroup F] [Finite E] [Finite K]

private def sumFibreEquiv (Q : E → F) (N : K → F) (c : F) :
    {p : E × K // Q p.1+N p.2=c} ≃ Σ e : E, {t : K // N t=c-Q e} where
  toFun p := ⟨p.val.1, ⟨p.val.2, eq_sub_iff_add_eq.mpr
    (by simpa only [add_comm] using p.property)⟩⟩
  invFun p := ⟨(p.1,p.2.val), by
    have h := eq_sub_iff_add_eq.mp p.2.property
    simpa only [add_comm] using h⟩
  left_inv p := rfl
  right_inv p := rfl

theorem sum_fibre_card_recurrence (Q : E → F) (N : K → F) (q : ℕ)
    (hzero : Nat.card {t : K // N t=0}=1)
    (hnonzero : ∀ a : F, a ≠ 0 → Nat.card {t : K // N t=a}=q+1) (c : F) :
    Nat.card {p : E × K // Q p.1+N p.2=c} + q*Nat.card {e : E // Q e=c} =
      (q+1)*Nat.card E := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype K := Fintype.ofFinite K
  have hgood : ∀ e : {e : E // Q e=c}, c-Q e.val=0 := by
    intro e
    rw [e.property,sub_self]
  have hbad : ∀ e : {e : E // ¬Q e=c}, c-Q e.val ≠ 0 := by
    intro e he
    exact e.property (sub_eq_zero.mp he).symm
  have hgoodSum : (∑ e : {e : E // Q e=c}, Nat.card {t : K // N t=c-Q e.val}) =
      Nat.card {e : E // Q e=c} := by
    simp_rw [hgood,hzero]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      Nat.card_eq_fintype_card,Nat.cast_id]
  have hbadSum : (∑ e : {e : E // ¬Q e=c}, Nat.card {t : K // N t=c-Q e.val}) =
      (q+1)*Nat.card {e : E // ¬Q e=c} := by
    simp_rw [hnonzero _ (hbad _)]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      Nat.card_eq_fintype_card,Nat.cast_id,Nat.mul_comm]
  have hsplit : Nat.card {p : E × K // Q p.1+N p.2=c} =
      Nat.card {e : E // Q e=c}+(q+1)*Nat.card {e : E // ¬Q e=c} := by
    rw [Nat.card_congr (sumFibreEquiv Q N c),Nat.card_sigma,
      ← Fintype.sum_subtype_add_sum_subtype (fun e : E => Q e=c)
        (fun e : E => Nat.card {t : K // N t=c-Q e}),hgoodSum,hbadSum]
  have htotal : Nat.card {e : E // Q e=c}+Nat.card {e : E // ¬Q e=c}=Nat.card E := by
    rw [←Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun e : E => Q e=c))
  rw [hsplit,←htotal]
  ring

theorem two_state_step (Q : E → F) (N : K → F) (q A B : ℕ)
    (hzero : Nat.card {t : K // N t=0}=1)
    (hnonzero : ∀ a : F, a ≠ 0 → Nat.card {t : K // N t=a}=q+1)
    (hQzero : Nat.card {e : E // Q e=0}=A)
    (hQnonzero : ∀ a : F, a ≠ 0 → Nat.card {e : E // Q e=a}=B) :
    (Nat.card {p : E × K // Q p.1+N p.2=0}+q*A=(q+1)*Nat.card E) ∧
    ∀ c : F, c ≠ 0 →
      Nat.card {p : E × K // Q p.1+N p.2=c}+q*B=(q+1)*Nat.card E := by
  constructor
  · simpa only [hQzero] using sum_fibre_card_recurrence Q N q hzero hnonzero 0
  · intro c hc
    simpa only [hQnonzero c hc] using sum_fibre_card_recurrence Q N q hzero hnonzero c

end SymmetricSubgroupAsymptotics.FiniteNormSumFibreRecurrence
