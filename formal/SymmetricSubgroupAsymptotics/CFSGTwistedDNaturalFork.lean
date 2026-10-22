import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkTorus
import SymmetricSubgroupAsymptotics.CFSGSerreForkDiagram

/-! The pinned D-fork diagram acts on the literal natural matrices by
interchanging the final positive/negative coordinate pair. This is a
matrix identity, not a recognition of a twisted fixed or derived group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFork
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
variable (K : Type) [Field K]

theorem flip_pos (s : ℕ) (i : Fin (s + 2)) :
    flip s (Sum.inl i) = if i = last s then Sum.inr i else Sum.inl i := by
  by_cases hi : i = last s
  · subst i
    simp [CFSGOrthogonalDGenerationForkTorus.flip]
  · simp [CFSGOrthogonalDGenerationForkTorus.flip, Equiv.swap_apply_def, hi, Ne.symm hi]

theorem flip_neg (s : ℕ) (i : Fin (s + 2)) :
    flip s (Sum.inr i) = if i = last s then Sum.inl i else Sum.inr i := by
  by_cases hi : i = last s
  · subst i
    simp [CFSGOrthogonalDGenerationForkTorus.flip]
  · simp [CFSGOrthogonalDGenerationForkTorus.flip, Equiv.swap_apply_def, hi, Ne.symm hi]

theorem previous_last (s : ℕ) : previous (s + 2) (last s) = pen s := by
  apply Fin.ext
  simp [previous, last, pen]

theorem twist_last (s : ℕ) : CFSG.Models.dTwist (last s) = pen s := by
  apply Fin.ext
  simp [CFSG.Models.dTwist, last, pen]

theorem twist_pen (s : ℕ) : CFSG.Models.dTwist (pen s) = last s := by
  apply Fin.ext
  simp [CFSG.Models.dTwist, last, pen]

theorem flip_involutive (s : ℕ) : Function.Involutive (flipAlgebra K s) := by
  intro A
  ext i j
  change A ((flip s).symm ((flip s).symm i))
    ((flip s).symm ((flip s).symm j)) = A i j
  simp [CFSGOrthogonalDGenerationForkTorus.flip]

theorem positive_last (s : ℕ) :
    flipAlgebra K s (positive K (s + 2) (last s)) = positive K (s + 2) (pen s) := by
  have hl : ¬ (last s).val + 1 < s + 2 := by simp [last]
  have hp : (pen s).val + 1 < s + 2 := by simp [pen]
  have hs : (⟨(pen s).val + 1, hp⟩ : Fin (s + 2)) = last s := by
    apply Fin.ext
    simp [pen, last]
  rw [positive, dif_neg hl, previous_last, map_sub, flip_single, flip_single,
    flip_pos, flip_neg, flip_pos, flip_neg,
    if_neg (pen_ne_last s), if_pos rfl, if_pos rfl, if_neg (pen_ne_last s)]
  rw [positive, dif_pos hp, hs]

theorem positive_pen (s : ℕ) :
    flipAlgebra K s (positive K (s + 2) (pen s)) = positive K (s + 2) (last s) := by
  rw [← positive_last K s]
  exact flip_involutive K s _

theorem positive_all (s : ℕ) (i : Fin (s + 2)) :
    flipAlgebra K s (positive K (s + 2) i) =
      positive K (s + 2) (CFSG.Models.dTwist i) := by
  by_cases hil : i = last s
  · subst i
    rw [twist_last]
    exact positive_last K s
  by_cases hip : i = pen s
  · subst i
    rw [twist_pen]
    exact positive_pen K s
  have hival : i.val ≠ s + 1 := by
    intro h
    apply hil
    apply Fin.ext
    simpa [last] using h
  have hipval : i.val ≠ s := by
    intro h
    apply hip
    apply Fin.ext
    simpa [pen] using h
  have hi : i.val + 1 < s + 2 := by have hb := i.isLt; omega
  let j : Fin (s + 2) := ⟨i.val + 1, hi⟩
  have hjl : j ≠ last s := by
    intro h
    have hv := congrArg Fin.val h
    change i.val + 1 = s + 1 at hv
    omega
  have htw : CFSG.Models.dTwist i = i := by
    simp only [CFSG.Models.dTwist, dif_pos (show 2 ≤ s + 2 by omega)]
    simp only [show s + 2 - 2 = s by omega, show s + 2 - 1 = s + 1 by omega,
      if_neg hipval, if_neg hival]
  rw [htw, positive, dif_pos hi, map_sub, flip_single, flip_single]
  change Matrix.single (flip s (Sum.inl i)) (flip s (Sum.inl j)) 1 -
    Matrix.single (flip s (Sum.inr j)) (flip s (Sum.inr i)) 1 = _
  simp only [flip_pos, flip_neg, if_neg hil, if_neg hjl]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFork
