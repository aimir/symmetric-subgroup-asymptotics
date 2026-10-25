import Mathlib.Data.Finset.Card
import Mathlib.Data.Finite.Card
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! Actual cut sets with gaps at least five inject into one of six
choices per consecutive block of five positions. The code retains each
cut's exact block and remainder; no partition count is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiveSeparatedCutCardinality

def SeparatedCuts (n : ℕ) :=
  {s : Finset (Fin n) // ∀ i ∈ s, ∀ j ∈ s, i.val < j.val → i.val + 5 ≤ j.val}

theorem same_block_eq {n : ℕ} (s : SeparatedCuts n) (i j : Fin n)
    (hi : i ∈ s.val) (hj : j ∈ s.val) (he : i.val / 5 = j.val / 5) : i = j := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hgap := s.property i hi j hj hij
    omega
  · have hgap := s.property j hj i hi hji
    omega

def cutCode {n : ℕ} (s : SeparatedCuts n) : Fin ((n + 4) / 5) → Option (Fin 5) :=
  fun b => if h : ∃ i : Fin n, i ∈ s.val ∧ i.val / 5 = b.val then
    some ⟨(Classical.choose h).val % 5, Nat.mod_lt _ (by decide)⟩ else none

theorem cutCode_eq_some {n : ℕ} (s : SeparatedCuts n) (i : Fin n) (hi : i ∈ s.val) :
    cutCode s ⟨i.val / 5,by omega⟩ = some ⟨i.val % 5,Nat.mod_lt _ (by decide)⟩ := by
  have h : ∃ j : Fin n, j ∈ s.val ∧ j.val / 5 = i.val / 5 := ⟨i,hi,rfl⟩
  rw [cutCode,dif_pos h]
  apply congrArg some
  apply Fin.ext
  have he := same_block_eq s (Classical.choose h) i (Classical.choose_spec h).1 hi
    (Classical.choose_spec h).2
  exact congrArg (fun j : Fin n => j.val % 5) he

theorem mem_of_cutCode_eq_some {n : ℕ} (s : SeparatedCuts n) (i : Fin n)
    (he : cutCode s ⟨i.val / 5,by omega⟩ =
      some ⟨i.val % 5,Nat.mod_lt _ (by decide)⟩) : i ∈ s.val := by
  unfold cutCode at he
  split_ifs at he with h
  · have hs := Classical.choose_spec h
    have hm : (Classical.choose h).val % 5 = i.val % 5 :=
      congrArg Fin.val (Option.some.inj he)
    have hd : (Classical.choose h).val / 5 = i.val / 5 := hs.2
    have hi : Classical.choose h = i := Fin.ext (by omega)
    exact hi ▸ hs.1

theorem cutCode_injective (n : ℕ) : Function.Injective (@cutCode n) := by
  intro s t he
  apply Subtype.ext
  ext i
  constructor
  · intro hi
    apply mem_of_cutCode_eq_some t i
    exact (congrFun he ⟨i.val / 5,by omega⟩).symm.trans (cutCode_eq_some s i hi)
  · intro hi
    apply mem_of_cutCode_eq_some s i
    exact (congrFun he ⟨i.val / 5,by omega⟩).trans (cutCode_eq_some t i hi)

theorem separatedCuts_card_le (n : ℕ) :
    Nat.card (SeparatedCuts n) ≤ 6 ^ ((n + 4) / 5) := by
  have h := Nat.card_le_card_of_injective (@cutCode n) (cutCode_injective n)
  simpa only [Nat.card_fun,Finite.card_option,Nat.card_fin] using h

end SymmetricSubgroupAsymptotics.FiveSeparatedCutCardinality
