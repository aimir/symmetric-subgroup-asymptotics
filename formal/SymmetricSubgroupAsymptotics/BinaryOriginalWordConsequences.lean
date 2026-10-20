import SymmetricSubgroupAsymptotics.BinaryTransitiveProperNormalQuarterPlusOne
import SymmetricSubgroupAsymptotics.BinaryExcessWeightedTail
import SymmetricSubgroupAsymptotics.MarkedC4ActualCaseIITargetStructure
import Mathlib.Data.Fintype.Perm

/-! Ordinary RDT5.5 is a consequence of the retained exact RDT5.3 input
and the proved intrinsic proper-normal ceiling. The filtration uses the
original subdirect subgroup, its literal maximal full tail, and the same
normal subgroup. No stronger proper-normal classification is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

open MarkedC4 MarkedC4.RDTExcessStructure MarkedC4.RDTOriginalWordStructure

private theorem proper_normalGen_eq_zero_of_degree_le_two
    (n : ℕ) (hn : n ≤ 2) (G : Subgroup (Equiv.Perm (Fin n)))
    (V : Subgroup G) [V.Normal] (hproper : V ≠ ⊤) : normalGen V = 0 := by
  have hperm : Nat.card (Equiv.Perm (Fin n)) ≤ 2 := by
    rw [Nat.card_perm, Nat.card_fin]
    interval_cases n <;> norm_num
  have hG : Nat.card G ≤ 2 := (Subgroup.card_le_card_group G).trans hperm
  have hind : 2 ≤ V.index := V.one_lt_index_of_ne_top hproper
  have hm := V.card_mul_index
  have hpos : 0 < Nat.card V := Nat.card_pos
  have hV : Nat.card V ≤ 1 := by nlinarith
  have hp := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card V
  have hpzero : 2 ^ normalGen V ≤ 2 ^ 0 := by simpa only [pow_zero] using hp.trans hV
  have hzero := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpzero
  omega

/-- The three exact dependent-factor prices need only the retained
RDT5.3 conclusion and the intrinsic proper-normal excess-one bound. -/
theorem binary_proper_normal_prices_of_proposition53
    (h53 : MarkedC4.ActualCaseIITargetStructure.PublishedProposition53Binary)
    (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : IsPGroup 2 G) (htrans : ∀ x y : Fin n, ∃ g : G, g.val x = y)
    (V : Subgroup G) [V.Normal] (hproper : V ≠ ⊤) :
    (normalGen V : ℝ) ≤ (3 / 8 : ℝ) * n ∧
      (¬(HasExcess G n 2 ∧ n = 8) → (normalGen V : ℝ) ≤ (5 / 16 : ℝ) * n) ∧
      (¬HasExcess G n 2 → (normalGen V : ℝ) ≤ (n : ℝ) / 4) := by
  have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  by_cases hn : n ≤ 2
  · have hz := proper_normalGen_eq_zero_of_degree_le_two n hn G V hproper
    simp only [hz, Nat.cast_zero]
    constructor
    · positivity
    constructor
    · intro _; positivity
    · intro _; positivity
  · have hnlarge : 2 < n := by omega
    by_cases hhigh : (n : ℝ) / 4 < normalGen V
    · obtain ⟨i, hi, hexcess, _, honly, hdegree⟩ :=
        h53 n G hnlarge hG htrans ⟨V, inferInstance, hhigh⟩
      have hi2 : i = 2 := hi.resolve_left (fun hi1 => hproper (honly hi1 V inferInstance hhigh))
      subst i
      have hdegree' := hdegree rfl
      letI : MulAction.IsPretransitive G (Fin n) := ⟨htrans⟩
      have hb := twoGroup_transitive_proper_normalGen_le_quarter_add_one G hG V hproper
      simp only [Nat.card_fin] at hb
      have hd := Nat.div_mul_le_self n 4
      have hnat : 4 * normalGen V ≤ n + 4 := by omega
      have hreal : (4 : ℝ) * normalGen V ≤ n + 4 := by exact_mod_cast hnat
      have hn8 : 8 ≤ n := by rcases hdegree' with h | h | h <;> omega
      have hn8R : (8 : ℝ) ≤ n := by exact_mod_cast hn8
      refine ⟨by linarith, ?_, fun hno => False.elim (hno hexcess)⟩
      intro hno
      have hn16 : 16 ≤ n := by
        rcases hdegree' with h8 | h16 | h32
        · exact False.elim (hno ⟨hexcess, h8⟩)
        · omega
        · omega
      have hn16R : (16 : ℝ) ≤ n := by exact_mod_cast hn16
      linarith
    · have hb : (normalGen V : ℝ) ≤ (n : ℝ) / 4 := le_of_not_gt hhigh
      exact ⟨by linarith, fun _ => by linarith, fun _ => hb⟩

/-- Exact ordinary RDT5.5 on the original physical factor actions follows
from retained ordinary RDT5.3. The maximal tail and every dependent
coordinate are exactly the ones in the published interface. -/
theorem publishedTheorem55Binary_of_proposition53
    (h53 : MarkedC4.ActualCaseIITargetStructure.PublishedProposition53Binary) :
    PublishedTheorem55Binary := by
  intro t n K hK htrans L hfull tail hmax N hN
  letI := hN
  have hlocal (i : Fin t) (V : Subgroup (K i)) [V.Normal] (hproper : V ≠ ⊤) :=
    binary_proper_normal_prices_of_proposition53 h53 (n i) (K i) (hK i) (htrans i) V hproper
  refine ⟨BinaryExcessWeightedTail.normalGen_le n K hK L hfull tail hmax N (3 / 8)
    (fun i _ V hV hproper => by letI := hV; exact (hlocal i V hproper).1), ?_, ?_⟩
  · intro hno
    exact BinaryExcessWeightedTail.normalGen_le n K hK L hfull tail hmax N (5 / 16)
      (fun i hi V hV hproper => by letI := hV; exact (hlocal i V hproper).2.1 (hno i hi))
  · intro hno
    have hh := BinaryExcessWeightedTail.normalGen_le n K hK L hfull tail hmax N (1 / 4)
      (fun i hi V hV hproper => by
        letI := hV
        simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using (hlocal i V hproper).2.2 (hno i hi))
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hh

end SymmetricSubgroupAsymptotics
