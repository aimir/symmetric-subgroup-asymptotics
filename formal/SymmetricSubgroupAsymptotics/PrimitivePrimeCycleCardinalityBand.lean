import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Finite.Card
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! A primitive action containing one actual prime cycle has a large
ordered-tuple orbit. We use the proved multiple-primitivity criterion,
not the unfinished prime-cycle alternating-containment theorem. The
original permutation subgroup and its actual cardinality are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitivePrimeCycleCardinalityBand
open MulAction Equiv.Perm

/-- The actual ordered-tuple orbit supplies the descending-factorial
cardinality bound, without requiring a faithful action. -/
theorem descFactorial_le_card_of_multiple_pretransitive
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (k : ℕ) (hk : k ≤ Nat.card X)
    (htrans : IsMultiplyPretransitive G X k) :
    (Nat.card X).descFactorial k ≤ Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : IsMultiplyPretransitive G X k := htrans
  obtain ⟨t⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin k) ≤ Fintype.card X by
      simpa only [Fintype.card_fin,Nat.card_eq_fintype_card] using hk)
  have hsurj : Function.Surjective (fun g : G => g • t) := by
    intro y
    exact exists_smul_eq G t y
  have hcard := Nat.card_le_card_of_surjective (fun g : G => g • t) hsurj
  simpa only [Nat.card_eq_fintype_card,Fintype.card_embedding_eq,
    Fintype.card_fin] using hcard

/-- Below twice the prime, the SAME actual element is a single cycle;
its prime support makes the complement fixer primitive. -/
theorem descFactorial_le_card_of_prime_order
    {X : Type*} [Fintype X] (P : Subgroup (Equiv.Perm X))
    (hP : IsPreprimitive P X) (p : ℕ) (hp : p.Prime)
    (g : Equiv.Perm X) (hg : g ∈ P) (horder : orderOf g = p)
    (hlarge : p < Nat.card X) (hsmall : Nat.card X < 2*p) :
    (Nat.card X).descFactorial (Nat.card X-p+1) ≤ Nat.card P := by
  classical
  have hcycle : g.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by simpa only [horder] using hp)
    (by simpa only [Nat.card_eq_fintype_card,horder] using hsmall)
  have hsupport : g.support.card = p := hcycle.orderOf.symm.trans horder
  have hfixcard :
      Nat.card (SubMulAction.ofFixingSubgroup P (g.supportᶜ : Set X)) = p := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype,←hsupport]
    apply congr_arg
    ext x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  haveI : IsPretransitive (fixingSubgroup P (g.supportᶜ : Set X))
      (SubMulAction.ofFixingSubgroup P (g.supportᶜ : Set X)) :=
    Equiv.Perm.isPretransitive_of_isCycle_mem hcycle hg
  have hfixprim : IsPreprimitive (fixingSubgroup P (g.supportᶜ : Set X))
      (SubMulAction.ofFixingSubgroup P (g.supportᶜ : Set X)) :=
    IsPreprimitive.of_prime_card (by simpa only [hfixcard] using hp)
  have hsum : g.support.card + (g.supportᶜ : Set X).ncard = Nat.card X := by
    simpa only [Set.ncard_coe_finset] using
      Set.ncard_add_ncard_compl (g.support : Set X)
  have hcomp : (g.supportᶜ : Set X).ncard = (Nat.card X-p-1)+1 := by
    rw [hsupport] at hsum
    omega
  have hp2 := hp.two_le
  have hmulti : IsMultiplyPreprimitive P X ((Nat.card X-p-1)+2) :=
    hP.isMultiplyPreprimitive hcomp (by omega) hfixprim
  have heq : (Nat.card X-p-1)+2 = Nat.card X-p+1 := by omega
  rw [heq] at hmulti
  letI : IsMultiplyPreprimitive P X (Nat.card X-p+1) := hmulti
  exact descFactorial_le_card_of_multiple_pretransitive
    (Nat.card X-p+1) (by omega) inferInstance

/-- This small integer seed is checked in the kernel by the primary
selected check; it is not obtained from a numerical producer. -/
theorem oneOhNine_pow_twelve_gt_eight_pow_twentySix :
    8^26 < (109 : ℕ)^12 := by norm_num

/-- A primitive action of the SAME group, whose order is at most 8^26,
cannot have degree120..217 while containing an element of order109. -/
theorem degree_lt_oneTwenty_of_order_oneOhNine
    {X : Type*} [Fintype X] (P : Subgroup (Equiv.Perm X))
    (hP : IsPreprimitive P X) (g : Equiv.Perm X) (hg : g ∈ P)
    (horder : orderOf g = 109) (hsmall : Nat.card X < 218)
    (hcard : Nat.card P ≤ 8^26) : Nat.card X < 120 := by
  by_contra hnot
  have hlarge : 120 ≤ Nat.card X := by omega
  have hdesc := descFactorial_le_card_of_prime_order P hP 109
    (by decide +kernel) g hg horder (by omega) (by omega)
  have hpow := Nat.pow_sub_le_descFactorial (Nat.card X) (Nat.card X-109+1)
  have hbase : Nat.card X+1-(Nat.card X-109+1) = 109 := by omega
  rw [hbase] at hpow
  have hexp : 12 ≤ Nat.card X-109+1 := by omega
  have hmono := Nat.pow_le_pow_right (by norm_num : 1 ≤ (109 : ℕ)) hexp
  have hbound : (109 : ℕ)^12 ≤ 8^26 := hmono.trans (hpow.trans (hdesc.trans hcard))
  exact (not_le_of_gt oneOhNine_pow_twelve_gt_eight_pow_twentySix) hbound

end SymmetricSubgroupAsymptotics.PrimitivePrimeCycleCardinalityBand
