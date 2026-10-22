import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadicalSupport
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalMiddle

/-! The actual fixed middle embedding retains displacement support at
the two embedded natural coordinates. No unipotent-derived claim is
made for the smaller source group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent

theorem naturalFixedMiddleHom_apply (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed s q) (i j : Index (Fin (s + 1))) :
    ((naturalFixedMiddleHom q s g).val.val : Mat (q.Extension 2) (s + 2))
      (splitEquiv s i) (splitEquiv s j) =
      middleArray (g.val.val : Mat (q.Extension 2) s) i j := by
  change Matrix.reindex (splitEquiv s) (splitEquiv s)
    (middleArray (g.val.val : Mat (q.Extension 2) s))
      (splitEquiv s i) (splitEquiv s j) = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem naturalFixedMiddleHom_support (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed s q) (a b : Fin (s + 1))
    (hd : ∀ i, (g.val.val : Mat (q.Extension 2) s) i i = 1)
    (hs : ∀ i j, i ≠ a → j ≠ b →
      (g.val.val : Mat (q.Extension 2) s) i j = (1 : Mat (q.Extension 2) s) i j) :
    (∀ i, ((naturalFixedMiddleHom q s g).val.val : Mat (q.Extension 2) (s + 2)) i i = 1) ∧
    ∀ i j, i ≠ splitEquiv s (.inr (.inl a)) →
      j ≠ splitEquiv s (.inr (.inl b)) →
      ((naturalFixedMiddleHom q s g).val.val : Mat (q.Extension 2) (s + 2)) i j =
        (1 : Mat (q.Extension 2) (s + 2)) i j := by
  constructor
  · intro i
    obtain ⟨x, rfl⟩ := (splitEquiv s).surjective i
    rw [naturalFixedMiddleHom_apply]
    rcases x with u | (i | u)
    · rfl
    · exact hd i
    · rfl
  · intro i j hi hj
    obtain ⟨x, rfl⟩ := (splitEquiv s).surjective i
    obtain ⟨y, rfl⟩ := (splitEquiv s).surjective j
    rw [naturalFixedMiddleHom_apply]
    have he : (1 : Mat (q.Extension 2) (s + 2)) (splitEquiv s x) (splitEquiv s y) =
        (1 : Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) x y := by
      simp only [Matrix.one_apply, (splitEquiv s).injective.eq_iff]
    rw [he]
    rcases x with u | (i | u) <;> rcases y with v | (j | v)
    all_goals try cases u
    all_goals try cases v
    all_goals try { simp [middleArray, Matrix.one_apply] }
    have hia : i ≠ a := by intro h; subst i; exact hi rfl
    have hjb : j ≠ b := by intro h; subst j; exact hj rfl
    simpa only [middleArray, Matrix.one_apply, Sum.inr.injEq, Sum.inl.injEq] using hs i j hia hjb

theorem middle_fixedRadical_support (q : CFSG.PrimePower) (s : ℕ)
    (g : fixedRadical q s) :
    (∀ i, ((naturalFixedMiddleHom q (s + 2) g.val).val.val : Mat (q.Extension 2) (s + 4)) i i = 1) ∧
    ∀ i j, i ≠ splitEquiv (s + 2) (.inr (.inl 0)) →
      j ≠ splitEquiv (s + 2) (.inr (.inl (Fin.last (s + 2)))) →
      ((naturalFixedMiddleHom q (s + 2) g.val).val.val : Mat (q.Extension 2) (s + 4)) i j =
        (1 : Mat (q.Extension 2) (s + 4)) i j := by
  obtain ⟨hd, hs⟩ := (mem_fixedRadical_iff_natural_support q s g.val).mp g.property
  exact naturalFixedMiddleHom_support q (s + 2) g.val 0 (Fin.last (s + 2)) hd hs

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
