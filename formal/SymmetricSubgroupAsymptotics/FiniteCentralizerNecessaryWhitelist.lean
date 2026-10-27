import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Card

/-! Upper-count an actual centralizer through a finite ambient chart and
any necessary original-image predicate. Whitelist entries need not be
original group elements. Duplicates and false positives only weaken the
upper bound; no membership converse or commuter-word lower bound is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteCentralizerNecessaryWhitelist

theorem centralizer_card_le_whitelist
    {G H I : Type*} [Group G] [Group H]
    (rho : G →* H) (faithful : Function.Injective rho) (a : G)
    (chart : I → H)
    (complete : ∀ z : H, z * rho a = rho a * z → ∃ i, chart i = z)
    (necessary : H → Prop) (source_necessary : ∀ g : G, necessary (rho g))
    (accepted : Finset I)
    (reject : ∀ i : I, chart i * rho a = rho a * chart i →
      necessary (chart i) → i ∈ accepted) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) ≤ accepted.card := by
  let C := Subgroup.centralizer ({a} : Set G)
  have hc (g : C) : rho g.val * rho a = rho a * rho g.val := by
    simpa only [←map_mul] using congrArg rho
      (Subgroup.mem_centralizer_singleton_iff.mp g.property)
  let code : C → I := fun g => Classical.choose (complete (rho g.val) (hc g))
  have hcode (g : C) : chart (code g) = rho g.val :=
    Classical.choose_spec (complete (rho g.val) (hc g))
  have hm (g : C) : code g ∈ accepted := by
    apply reject (code g)
    · rw [hcode]
      exact hc g
    · rw [hcode]
      exact source_necessary g.val
  let f : C → accepted := fun g => ⟨code g,hm g⟩
  have hf : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply faithful
    have hi : code g = code h := congrArg Subtype.val he
    rw [←hcode g,←hcode h,hi]
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
    Nat.card_le_card_of_injective f hf

end SymmetricSubgroupAsymptotics.FiniteCentralizerNecessaryWhitelist
