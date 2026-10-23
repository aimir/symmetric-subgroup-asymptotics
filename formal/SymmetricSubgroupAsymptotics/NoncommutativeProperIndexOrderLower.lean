import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Lean.Elab.Tactic.Omega

/-! Every finite noncommutative group has a nontrivial proper cyclic
subgroup. Thus a literal lower bound b on EVERY proper index gives an
order lower bound2b, without a simple-group order formula or index-square
hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NoncommutativeProperIndexOrderLower

theorem twice_le_card {G : Type*} [Group G] [Finite G]
    (hn : ¬IsMulCommutative G) (b : ℕ)
    (hindex : ∀ H : Subgroup G, H ≠ ⊤ → b ≤ H.index) : 2 * b ≤ Nat.card G := by
  classical
  have hnot : ¬∀ a c : G, a * c = c * a := fun h => hn (isMulCommutative_iff.mpr h)
  obtain ⟨a, ha⟩ := not_forall.mp hnot
  obtain ⟨c, hac⟩ := not_forall.mp ha
  have hane : a ≠ 1 := by
    intro he
    apply hac
    rw [he, one_mul, mul_one]
  let C : Subgroup G := Subgroup.zpowers a
  have hC : C ≠ ⊤ := by
    intro ht
    have haC : a ∈ C := Subgroup.mem_zpowers a
    have hcC : c ∈ C := by rw [ht]; trivial
    have hh := isMulCommutative_iff.mp (inferInstance : IsMulCommutative C)
      (⟨a, haC⟩ : C) (⟨c, hcC⟩ : C)
    exact hac (congrArg (fun z : C => (z : G)) hh)
  let x : C := ⟨a, Subgroup.mem_zpowers a⟩
  have hx : x ≠ 1 := by
    intro he
    exact hane (congrArg (fun z : C => (z : G)) he)
  letI : Nontrivial C := ⟨⟨x, 1, hx⟩⟩
  have htwo : 2 ≤ Nat.card C := by
    have hh : 1 < Nat.card C := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  exact (Nat.mul_le_mul htwo (hindex C hC)).trans_eq C.card_mul_index

end SymmetricSubgroupAsymptotics.NoncommutativeProperIndexOrderLower
