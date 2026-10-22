import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalSupport
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryFixedRadicalGroup

/-! Exact natural-coordinate characterization of the actual fixed
radical. Its diagonal and two-axis displacement support are proved by
the actual inverse coordinate equivalence, in both directions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent

theorem blockFixedMatrixHom_apply (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q) (i j : Index (Fin (s + 1))) :
    (blockFixedMatrixHom q s g : Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) i j =
      (g.val.val : Mat (q.Extension 2) (s + 2)) (splitEquiv s i) (splitEquiv s j) := by
  change Matrix.reindex (splitEquiv s).symm (splitEquiv s).symm
    (g.val.val : Mat (q.Extension 2) (s + 2)) i j = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]

theorem mem_fixedRadical_iff_natural_support (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q) :
    g ∈ fixedRadical q s ↔
      (∀ i, (g.val.val : Mat (q.Extension 2) (s + 2)) i i = 1) ∧
      ∀ i j, i ≠ 0 → j ≠ Fin.last (s + 2) →
        (g.val.val : Mat (q.Extension 2) (s + 2)) i j = (1 : Mat (q.Extension 2) (s + 2)) i j := by
  change blockFixedMatrixHom q s g ∈ arrayGroup ↔ _
  rw [mem_arrayGroup_iff_support]
  constructor
  · rintro ⟨hd, hs⟩
    constructor
    · intro i
      obtain ⟨x, rfl⟩ := (splitEquiv s).surjective i
      simpa only [blockFixedMatrixHom_apply] using hd x
    · intro i j hi hj
      obtain ⟨x, rfl⟩ := (splitEquiv s).surjective i
      obtain ⟨y, rfl⟩ := (splitEquiv s).surjective j
      have hx : x ≠ .inl () := by intro h; subst x; exact hi rfl
      have hy : y ≠ .inr (.inr ()) := by intro h; subst y; exact hj rfl
      have h := hs x y hx hy
      rw [blockFixedMatrixHom_apply] at h
      simpa only [Matrix.one_apply, (splitEquiv s).injective.eq_iff] using h
  · rintro ⟨hd, hs⟩
    constructor
    · intro i
      rw [blockFixedMatrixHom_apply]
      exact hd _
    · intro i j hi hj
      rw [blockFixedMatrixHom_apply]
      have hx : splitEquiv s i ≠ 0 := by
        intro h
        apply hi
        exact (splitEquiv s).injective h
      have hy : splitEquiv s j ≠ Fin.last (s + 2) := by
        intro h
        apply hj
        exact (splitEquiv s).injective h
      have h := hs (splitEquiv s i) (splitEquiv s j) hx hy
      simpa only [Matrix.one_apply, (splitEquiv s).injective.eq_iff] using h

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
