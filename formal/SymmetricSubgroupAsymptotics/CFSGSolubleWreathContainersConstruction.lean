import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersCount
import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersStepCover

/-! Actual transitive soluble containers, constructed together with their
uniform counting bound. The induction records whole-point relabellings;
every covered source is contained as its original labelled subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers

theorem boundedTransitiveCover_exists (n : ℕ) :
    ∃ E : TransitiveSolubleContainerCover n,
      Nat.card E.Index ≤ 2 ^ containerBudget n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : 2 ≤ n
    · let below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val :=
        fun d => Classical.choose (ih d.val d.isLt)
      have hbelow (d : Fin n) :
          Nat.card (below d).Index ≤ 2 ^ containerBudget d.val :=
        Classical.choose_spec (ih d.val d.isLt)
      let E : TransitiveSolubleContainerCover n :=
        { Index := StepIndex n below
          finiteIndex := inferInstance
          group := stepGroup n below
          soluble := stepGroup_soluble n below
          covers := step_covers n below hn }
      refine ⟨E, ?_⟩
      exact stepIndex_card_le_budget n hn below hbelow
    · letI solubleWreathConstruction_smallPoints : Subsingleton (Fin n) :=
        ⟨fun a b => Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega)⟩
      let E : TransitiveSolubleContainerCover n :=
        { Index := Unit
          finiteIndex := inferInstance
          group := fun _ => ⊤
          soluble := fun _ => inferInstance
          covers := fun _ _ _ => ⟨(), le_top⟩ }
      refine ⟨E, ?_⟩
      change Nat.card Unit ≤ 2 ^ containerBudget n
      simpa only [Nat.card_eq_fintype_card, Fintype.card_unique] using
        (Nat.one_le_two_pow : 1 ≤ 2 ^ containerBudget n)

def transitiveCover (n : ℕ) : TransitiveSolubleContainerCover n :=
  Classical.choose (boundedTransitiveCover_exists n)

theorem transitiveCover_card_le (n : ℕ) :
    Nat.card (transitiveCover n).Index ≤ 2 ^ containerBudget n :=
  Classical.choose_spec (boundedTransitiveCover_exists n)

theorem transitiveCover_card_le_common_budget {d b : ℕ} (hdb : d ≤ b) :
    Nat.card (transitiveCover d).Index ≤ 2 ^ ((32 * logBudget b) * d) := by
  apply (transitiveCover_card_le d).trans
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  have h := Nat.mul_le_mul_left (32 * d) (logBudget_mono hdb)
  unfold containerBudget
  nlinarith

end SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
