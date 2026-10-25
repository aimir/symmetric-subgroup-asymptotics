import SymmetricSubgroupAsymptotics.SmallFibreKnownModelClassGap
import SymmetricSubgroupAsymptotics.CFSGPrimePowerSmallOrders
import SymmetricSubgroupAsymptotics.CFSGPSLTwoSmallFieldParameters

/-! Bounded rank/field parameters and complete small-fibre profiles.
These are parameter pairs, not actions or subgroup-catalogue rows.
The eleven higher-A pairs remain outside the proved profile. All B/C
and unitary parameters are now covered. The former ten unitary heads
and older conditional exclusions remain available for compatibility. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SmallFibreClassicalBoundedHeadParameters
open SmallFibreKnownModelClassGap

def typeAHeads : Finset (ℕ × ℕ) :=
  {(2,2),(2,3),(2,4),(3,2),(3,3),(3,4),(4,2),(4,3),(5,2),(6,2),(7,2)}

def unitaryHeads : Finset (ℕ × ℕ) :=
  {(2,3),(2,4),(2,5),(2,7),(2,8),(2,9),(3,2),(3,3),(3,4),(4,2)}

theorem typeAHeads_card : typeAHeads.card=11 := by decide +kernel

theorem unitaryHeads_card : unitaryHeads.card=10 := by decide +kernel

variable {S : Type} [Group S]

theorem unitary_closed (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : S ≃* CFSG.Models.TwistedA r q) : Profile S :=
  .unitaryComplete r hr q hsmall e

theorem pslTwo_parameters_of_not_closed (q : CFSG.PrimePower) (hq : 4≤q.order)
    (e : S ≃* CFSG.Models.A 1 q) (h : ¬Profile S) :
    q.order∈CFSGPSLTwoSmallFieldParameters.tinyOrders := by
  have hupper : q.order<51 := by
    by_contra hh
    exact h (.pslTwo q (by omega) e)
  rcases CFSGPSLTwoSmallFieldParameters.improved_or_tiny q hq hupper with hp | ht
  · exact (h (.pslTwoImproved q hp e)).elim
  · exact ht

theorem typeB_closed (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (e : S ≃* CFSG.Models.B r q) : Profile S := by
  by_cases hp : q.prime=2
  · exact .charTwoTypeBFull r hr q hp e
  · exact .oddTypeB r hr q hp e

theorem typeC_closed (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : S ≃* CFSG.Models.C r q) : Profile S := by
  by_cases hp : q.prime=2
  · exact .charTwoTypeCFull r hr q hp hsmall e
  · exact .oddTypeC r hr q hp e

private theorem order_ge_two (q : CFSG.PrimePower) : 2 ≤ q.order :=
  q.prime_isPrime.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.prime)

theorem typeA_parameters_of_not_closed (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (e : S ≃* CFSG.Models.A r q) (h : ¬Profile S) :
    (r,q.order) ∈ typeAHeads := by
  have hw : ¬(8 ≤ r ∨ (5 ≤ r ∧ 3 ≤ q.order) ∨ (4 ≤ r ∧ 4 ≤ q.order) ∨
      (r=3 ∧ 5 ≤ q.order) ∨ (r=2 ∧ 5 ≤ q.order)) :=
    fun hw => h (.typeAScaled r q hw e)
  have hq := order_ge_two q
  have hrange : r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 := by omega
  rcases hrange with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [typeAHeads] <;> omega

theorem unitary_parameters_of_not_closed (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2)
    (e : S ≃* CFSG.Models.TwistedA r q) (h : ¬Profile S) :
    (r,q.order) ∈ unitaryHeads := by
  have hw : ¬((r=2 ∧ 11 ≤ q.order) ∨ (r=3 ∧ 5 ≤ q.order)) :=
    fun hw => h (.unitaryLowRankTail r q hw e)
  have hh : ¬(4 ≤ r ∧ (r=4 → 3 ≤ q.order)) :=
    fun hh => h (.unitaryHigherCoupled r hh.1 q hh.2 e)
  have hq := order_ge_two q
  have h6 := CFSGPrimePowerSmallOrders.order_ne_six q
  have h10 : q.order≠10 := by
    have hn : ¬IsPrimePow (10:ℕ) := by decide +kernel
    intro he
    exact hn (he ▸ CFSGPrimePowerSmallOrders.order_isPrimePow q)
  have hrange : r=2 ∨ r=3 ∨ r=4 := by omega
  rcases hrange with rfl | rfl | rfl <;> simp [unitaryHeads] <;> omega

theorem typeB_parameters_of_not_closed (r : ℕ) (hr : 3 ≤ r)
    (q : CFSG.PrimePower) (e : S ≃* CFSG.Models.B r q) (h : ¬Profile S) :
    r=3 ∧ q.order=2 := by
  by_contra hh
  by_cases hp : q.prime=2
  · exact h (.charTwoTypeB r hr q hp hh e)
  · exact h (.oddTypeB r hr q hp e)

theorem typeC_parameters_of_not_closed (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2)
    (e : S ≃* CFSG.Models.C r q) (h : ¬Profile S) :
    r=3 ∧ q.order=2 := by
  by_contra hh
  by_cases hp : q.prime=2
  · exact h (.charTwoTypeC r hr q hp hsmall hh e)
  · exact h (.oddTypeC r hr q hp e)

end SymmetricSubgroupAsymptotics.SmallFibreClassicalBoundedHeadParameters
