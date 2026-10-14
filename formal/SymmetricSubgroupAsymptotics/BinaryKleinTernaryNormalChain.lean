import SymmetricSubgroupAsymptotics.BinaryFourAugmentationActions
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit
import SymmetricSubgroupAsymptotics.DirectProductNormalGenerators
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! The actual Klein-by-three complement has a normal chain. This follows
from its displayed three-cycle on the nonzero Klein vectors and its faithful
action, without identifying a group from its order or listing normal subgroups. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryKleinTernaryNormalChain

open BinaryFourBlockAugmentation SemidirectProduct

def kleinKernel : Subgroup Complement :=
  (SemidirectProduct.rightHom : Complement →* Ternary).ker

instance : kleinKernel.Normal :=
  inferInstanceAs (SemidirectProduct.rightHom : Complement →* Ternary).ker.Normal

theorem local_nonzero_transitive (p q : Local) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ z : Ternary, (kleinCyclicAction z (Multiplicative.ofAdd p)).toAdd = q := by
  have h : ∀ p q : Local, p ≠ 0 → q ≠ 0 →
      ∃ z : Ternary, (kleinCyclicAction z (Multiplicative.ofAdd p)).toAdd = q := by
    decide +kernel
  exact h p q hp hq

theorem kleinKernel_minimal (W : Subgroup Complement) (hW : W.Normal)
    (hWK : W ≤ kleinKernel) : W = ⊥ ∨ W = kleinKernel := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨w, hw, hne⟩ := W.bot_or_exists_ne_one.resolve_left hb
  have hwr : w.right = 1 := hWK hw
  have hwp : w.left.toAdd ≠ 0 := by
    intro hp
    apply hne
    exact SemidirectProduct.ext (Multiplicative.toAdd.injective hp) hwr
  apply le_antisymm hWK
  intro v hv
  have hvr : v.right = 1 := hv
  by_cases hvp : v.left.toAdd = 0
  · have hvone : v = 1 :=
      SemidirectProduct.ext (Multiplicative.toAdd.injective hvp) hvr
    simpa only [hvone] using W.one_mem
  obtain ⟨z, hz⟩ := local_nonzero_transitive w.left.toAdd v.left.toAdd hwp hvp
  have hc := hW.conj_mem w hw (inr z)
  have hwform : (inl w.left : Complement) = w := SemidirectProduct.ext rfl hwr.symm
  have he : (inr z : Complement) * w * (inr z)⁻¹ = v := by
    rw [← hwform, ← map_inv, ← inl_aut]
    apply SemidirectProduct.ext
    · exact Multiplicative.toAdd.injective hz
    · exact hvr.symm
  exact he ▸ hc

theorem kleinKernel_selfCentralizing (g : Complement)
    (hg : ∀ v ∈ kleinKernel, g * v = v * g) : g ∈ kleinKernel := by
  let p : Klein := Multiplicative.ofAdd ![1, 0]
  have hh := congrArg SemidirectProduct.left (hg (inl p) (by rfl))
  change g.left * kleinCyclicAction g.right p = p * kleinCyclicAction 1 g.left at hh
  rw [map_one] at hh
  change g.left * kleinCyclicAction g.right p = p * g.left at hh
  have ha : kleinCyclicAction g.right p = p :=
    mul_left_cancel (hh.trans (mul_comm p g.left))
  have detect : ∀ z : Ternary,
      (kleinCyclicAction z (Multiplicative.ofAdd ![1, 0])).toAdd = ![1, 0] → z = 1 := by
    decide +kernel
  exact detect g.right (congrArg Multiplicative.toAdd ha)

theorem kleinKernel_le_normal (N : Subgroup Complement) (hN : N.Normal) (hNb : N ≠ ⊥) :
    kleinKernel ≤ N := by
  letI := hN
  exact le_of_minimal_selfCentralizing kleinKernel kleinKernel_minimal
    kleinKernel_selfCentralizing N hNb

theorem ternary_subgroup_total (A B : Subgroup Ternary) : A ≤ B ∨ B ≤ A := by
  have hcard : Nat.card Ternary = 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Ternary ≃ ZMod 3), Nat.card_zmod]
  letI : Fact (Nat.card Ternary).Prime := ⟨by rw [hcard]; decide⟩
  rcases A.eq_bot_or_eq_top_of_prime_card with h | h
  · left
    rw [h]
    exact bot_le
  · right
    rw [h]
    exact le_top

theorem normal_total (A B : Subgroup Complement) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A := by
  by_cases hAb : A = ⊥
  · left; rw [hAb]; exact bot_le
  by_cases hBb : B = ⊥
  · right; rw [hBb]; exact bot_le
  let pi : Complement →* Ternary := SemidirectProduct.rightHom
  have hKA : pi.ker ≤ A := kleinKernel_le_normal A hA hAb
  have hKB : pi.ker ≤ B := kleinKernel_le_normal B hB hBb
  rcases ternary_subgroup_total (A.map pi) (B.map pi) with h | h
  · left
    calc
      A = (A.map pi).comap pi := (Subgroup.comap_map_eq_self hKA).symm
      _ ≤ (B.map pi).comap pi := Subgroup.comap_mono h
      _ = B := Subgroup.comap_map_eq_self hKB
  · right
    calc
      B = (B.map pi).comap pi := (Subgroup.comap_map_eq_self hKB).symm
      _ ≤ (A.map pi).comap pi := Subgroup.comap_mono h
      _ = A := Subgroup.comap_map_eq_self hKA

theorem normal_generating_singletons : ∀ N : Subgroup Complement, N.Normal →
    ∃ x : Fin 1 → Complement, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_singletons_of_finite_normal_total normal_total

theorem normalGen_le_one (N : Subgroup Complement) [N.Normal] : MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨x, hx⟩ := normal_generating_singletons N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem binary_subgroup_total (A B : Subgroup (Multiplicative Scalar)) : A ≤ B ∨ B ≤ A := by
  have hcard : Nat.card (Multiplicative Scalar) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative Scalar ≃ Scalar), Nat.card_zmod]
  letI : Fact (Nat.card (Multiplicative Scalar)).Prime := ⟨by rw [hcard]; decide⟩
  rcases A.eq_bot_or_eq_top_of_prime_card with h | h
  · left; rw [h]; exact bot_le
  · right; rw [h]; exact le_top

theorem product_normalGen_le_two (N : Subgroup (Complement × Multiplicative Scalar))
    [N.Normal] : MarkedC4.normalGen N ≤ 2 := by
  obtain ⟨x, hx⟩ := normal_generating_pairs_prod_of_normal_total normal_total
    (fun A B _ _ => binary_subgroup_total A B) N inferInstance
  exact normalGen_le_of_fin_tuple x hx

end BinaryKleinTernaryNormalChain
end SymmetricSubgroupAsymptotics

end
