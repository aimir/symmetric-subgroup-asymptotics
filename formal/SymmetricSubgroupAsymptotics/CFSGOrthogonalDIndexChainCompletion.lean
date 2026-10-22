import Mathlib.Data.Fin.Basic

/-! A reusable directed-root closure lemma. Positive chain directions
and the single last-to-first direction give every off-diagonal
direction, whenever actual three-distinct-index commutators provide
composition. The relation may describe full matrix root-line membership;
no group identification or generation hypothesis is hidden in it. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexChainCompletion

theorem complete_of_positive_and_last_zero (r : ℕ) (hr : 2 ≤ r)
    (R : Fin r → Fin r → Prop)
    (hpositive : ∀ i j, i < j → R i j)
    (hcorner : R ⟨r - 1, by omega⟩ ⟨0, by omega⟩)
    (hcompose : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → R i j → R j k → R i k) :
    ∀ i j, i ≠ j → R i j := by
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hlastFirst : last ≠ first := by
    intro h
    have he := congrArg Fin.val h
    change r - 1 = 0 at he
    omega
  have hfirst (i : Fin r) (hi : i ≠ first) : R i first := by
    by_cases hil : i = last
    · subst i
      exact hcorner
    · have hlt : i < last := by
        have hb := i.isLt
        have hn : i.val ≠ r - 1 := fun he => hil (Fin.ext he)
        change i.val < r - 1
        omega
      exact hcompose i last first hil hi hlastFirst (hpositive i last hlt) hcorner
  intro i j hij
  by_cases hi : i = first
  · subst i
    apply hpositive first j
    have hn : j.val ≠ 0 := fun he => hij (Fin.ext he).symm
    change 0 < j.val
    omega
  · by_cases hj : j = first
    · subst j
      exact hfirst i hi
    · apply hcompose i first j hi hij (Ne.symm hj) (hfirst i hi)
      apply hpositive first j
      have hn : j.val ≠ 0 := fun he => hj (Fin.ext he)
      change 0 < j.val
      omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexChainCompletion
