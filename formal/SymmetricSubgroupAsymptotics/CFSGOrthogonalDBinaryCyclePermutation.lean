import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The literal coordinate permutation of the binary D Coxeter word:
a signed cycle on the first r-1 pairs and a sign exchange on the last
pair. It is defined by the original chain cycle and crossed fork swaps. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryCyclePermutation
open CFSGOrthogonalDSerreMatrices

def forkPerm (s : ℕ) : Equiv.Perm (Index (s + 2)) :=
  Equiv.swap (Sum.inl (Fin.last s).castSucc) (Sum.inr (Fin.last (s + 1))) *
    Equiv.swap (Sum.inl (Fin.last (s + 1))) (Sum.inr (Fin.last s).castSucc)

def cyclePerm (s : ℕ) : Equiv.Perm (Index (s + 2)) :=
  (forkPerm s).trans (Equiv.sumCongr (finRotate (s + 2)) (finRotate (s + 2)))

theorem cyclePerm_shift (s : ℕ) (side : Bool) (j : ℕ) (hj : j < s) :
    cyclePerm s (if side then Sum.inr (⟨j, by omega⟩ : Fin (s + 2))
      else Sum.inl ⟨j, by omega⟩) =
      if side then Sum.inr (⟨j + 1, by omega⟩ : Fin (s + 2))
      else Sum.inl ⟨j + 1, by omega⟩ := by
  have hp : j ≠ s := by omega
  have hq : j ≠ s + 1 := by omega
  cases side <;>
    simp [cyclePerm, forkPerm, Equiv.swap_apply_def, Fin.ext_iff, hp, hq,
      finRotate_of_lt (show j < s + 1 by omega)]

theorem cyclePerm_positive_penultimate (s : ℕ) :
    cyclePerm s (Sum.inl (Fin.last s).castSucc) = Sum.inr (0 : Fin (s + 2)) := by
  simp [cyclePerm, forkPerm, Equiv.swap_apply_def, Fin.ext_iff]

theorem cyclePerm_negative_penultimate (s : ℕ) :
    cyclePerm s (Sum.inr (Fin.last s).castSucc) = Sum.inl (0 : Fin (s + 2)) := by
  simp [cyclePerm, forkPerm, Equiv.swap_apply_def, Fin.ext_iff]

theorem cyclePerm_positive_last (s : ℕ) :
    cyclePerm s (Sum.inl (Fin.last (s + 1))) = Sum.inr (Fin.last (s + 1)) := by
  simp [cyclePerm, forkPerm, Equiv.swap_apply_def, Fin.ext_iff,
    finRotate_of_lt (show s < s + 1 by omega)]

theorem cyclePerm_negative_last (s : ℕ) :
    cyclePerm s (Sum.inr (Fin.last (s + 1))) = Sum.inl (Fin.last (s + 1)) := by
  simp [cyclePerm, forkPerm, Equiv.swap_apply_def, Fin.ext_iff,
    finRotate_of_lt (show s < s + 1 by omega)]

def paired {r : ℕ} : Index r → Index r
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl i

theorem cyclePerm_paired (s : ℕ) (a : Index (s + 2)) :
    cyclePerm s (paired a) = paired (cyclePerm s a) := by
  have aux (side : Bool) (i : Fin (s + 2)) :
      cyclePerm s (if side then Sum.inl i else Sum.inr i) =
        paired (cyclePerm s (if side then Sum.inr i else Sum.inl i)) := by
    by_cases hi : i.val < s
    · have hp := cyclePerm_shift s false i.val hi
      have hn := cyclePerm_shift s true i.val hi
      cases side
      · simpa only [Bool.false_eq_true, if_false, paired] using
          hn.trans (congrArg paired hp).symm
      · simpa only [if_true, paired] using
          hp.trans (congrArg paired hn).symm
    · by_cases hp : i.val = s
      · have he : i = (Fin.last s).castSucc := Fin.ext hp
        subst i
        cases side <;>
          simp only [Bool.false_eq_true, if_false, if_true,
            cyclePerm_positive_penultimate, cyclePerm_negative_penultimate, paired]
      · have he : i = Fin.last (s + 1) := by
          apply Fin.ext
          have hb := i.isLt
          change i.val = s + 1
          omega
        subst i
        cases side <;>
          simp only [Bool.false_eq_true, if_false, if_true,
            cyclePerm_positive_last, cyclePerm_negative_last, paired]
  cases a with
  | inl i => exact aux false i
  | inr i => exact aux true i

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryCyclePermutation
