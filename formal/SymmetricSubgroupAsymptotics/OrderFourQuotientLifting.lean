import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.NormNum

/-! Actual order-four elements lift through finite surjections and are
incompatible with elementary actual Sylow two-subgroups. These statements
retain the original map and actual element; group-order divisibility alone
is never used as an order-four existence claim. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OrderFourQuotientLifting

theorem exists_of_four_dvd_orderOf {G : Type} [Group G] [Finite G]
    (g : G) (hg : 4 ∣ orderOf g) : ∃ x : G, orderOf x = 4 :=
  ⟨g^(orderOf g/4),orderOf_pow_orderOf_div (orderOf_pos g).ne' hg⟩

theorem exists_of_surjective {G Q : Type} [Group G] [Finite G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (q : Q) (hq : orderOf q = 4) :
    ∃ g : G, orderOf g = 4 := by
  obtain ⟨g,hg⟩ := hf q
  apply exists_of_four_dvd_orderOf g
  have hh := orderOf_map_dvd f g
  rwa [hg,hq] at hh

theorem no_order_four_of_elementary_sylows {G : Type} [Group G] [Finite G]
    (hel : ∀ P : Sylow 2 G, ∀ x : P, x^2 = 1) :
    ¬∃ g : G, orderOf g = 4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨g,hg⟩
  have hZ : IsPGroup 2 (Subgroup.zpowers g) := IsPGroup.of_card (n := 2)
    ((Nat.card_zpowers g).trans hg)
  obtain ⟨P,hP⟩ := hZ.exists_le_sylow
  let x : P := ⟨g,hP (Subgroup.mem_zpowers g)⟩
  have hs : g^2 = 1 := congrArg Subtype.val (hel P x)
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [hg] at hd
  norm_num at hd

end SymmetricSubgroupAsymptotics.OrderFourQuotientLifting
