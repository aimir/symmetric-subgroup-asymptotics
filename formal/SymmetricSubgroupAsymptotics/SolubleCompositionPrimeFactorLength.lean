import SymmetricSubgroupAsymptotics.ChiefAbelianCompositionLength
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Solvable

/-! For a finite soluble group the total prime-factor length of its order
is at most the length of every literal composition series. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

theorem soluble_cardFactors_le_compositionLength
    {G : Type} [Group G] [Finite G] [IsSolvable G]
    (t : SubnormalCompositionSeries G) :
    ArithmeticFunction.cardFactors (Nat.card G) ≤ t.chain.length := by
  have h := subgroupSeries_cardFactors_le_length t.chain.length
    (fun i => (t.chain i).val) (compositionSeries_strictMono t).monotone (by
      intro i
      obtain ⟨hn,hs⟩ := subnormalCover_quotient_simple
        (t.chain i.castSucc) (t.chain i.succ) (t.chain.step i)
      letI := hn
      letI := hs
      let Q := (t.chain i.succ).val ⧸ (t.chain i.castSucc).val.subgroupOf (t.chain i.succ).val
      letI : IsMulCommutative Q := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩⟩
      have hp : (Nat.card Q).Prime := IsSimpleGroup.prime_card
      change ArithmeticFunction.cardFactors (Nat.card Q) ≤ 1
      exact (ArithmeticFunction.cardFactors_apply_prime hp).le)
  have h0 : (t.chain 0).val=⊥ := t.head
  have hl : (t.chain (Fin.last t.chain.length)).val=⊤ := t.last
  have htop : Nat.card (⊤ : Subgroup G)=Nat.card G := Nat.card_congr Subgroup.topEquiv.toEquiv
  simpa only [h0,hl,Subgroup.relIndex_bot_left,htop] using h

end SymmetricSubgroupAsymptotics
