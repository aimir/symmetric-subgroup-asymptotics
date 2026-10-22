import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalFixedSpace

/-! The actual defining-fixed upper subgroup has common fixed space the
first natural coordinate line. Both directions use literal group entries:
radical elements detect all other coordinates, and upper-unitriangular
matrices fix the first column. No derived or whole-unitary premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

theorem reindex_mulVec_apply {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    (e : I ≃ J) (A : Matrix I I K) (x : J → K) (i : I) :
    (Matrix.reindex e e A *ᵥ x) (e i) = (A *ᵥ (x ∘ e)) i := by
  have h := Matrix.submatrix_mulVec_equiv A x e.symm e.symm
  have hh := congrArg (fun v : J → K => v (e i)) h
  simpa only [Matrix.reindex, Function.comp_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUnitaryCoordinates CFSGTwistedAUpperUnipotent

theorem naturalUnipotent_fixed_iff (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 3) → q.Extension 2) :
    (∀ g : naturalUnipotent (s + 2) q, (g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x = x) ↔
      (∀ i : Fin (s + 1), x (splitIndex s (.inr (.inl i))) = 0) ∧
        x (Fin.last (s + 2)) = 0 := by
  constructor
  · intro hx
    have hr : ∀ v b, Condition q s v b →
        upperArray (firstRow q s v) v b *ᵥ (x ∘ splitEquiv s) = x ∘ splitEquiv s := by
      intro v b hb
      have hg := hx (radicalElement q s v b hb)
      rw [radicalElement_matrix] at hg
      funext i
      have hi := congrArg (fun z : Fin (s + 3) → q.Extension 2 => z (splitEquiv s i)) hg
      dsimp only at hi
      rw [reindex_mulVec_apply] at hi
      exact hi
    exact (radicalArrays_fixed_iff q s (x ∘ splitEquiv s)).mp hr
  · rintro ⟨hm, hl⟩ g
    have hx : x = Pi.single 0 (x 0) := by
      funext i
      obtain ⟨z, rfl⟩ := (splitEquiv s).surjective i
      rcases z with u | (j | u)
      · cases u
        simp [splitEquiv, splitIndex]
      · have hne : splitEquiv s (.inr (.inl j)) ≠ 0 := by
          intro he
          have hv := congrArg (fun a : Fin (s + 3) => a.val) he
          change j.val + 1 = 0 at hv
          omega
        simpa [Pi.single_apply, hne, Ne.symm hne] using hm j
      · cases u
        have hne : (Fin.last (s + 2) : Fin (s + 3)) ≠ 0 := by
          intro he
          have hv := congrArg (fun a : Fin (s + 3) => a.val) he
          change s + 2 = 0 at hv
          omega
        change x (Fin.last (s + 2)) = (Pi.single (0 : Fin (s + 3)) (x 0) : Fin (s + 3) → q.Extension 2) (Fin.last (s + 2))
        simp [hl, Pi.single_apply, hne, Ne.symm hne]
    rw [hx, Matrix.mulVec_single]
    funext i
    change (g.val.val : Mat (q.Extension 2) (s + 2)) i 0 * x 0 = (Pi.single (0 : Fin (s + 3)) (x 0) : Fin (s + 3) → q.Extension 2) i
    by_cases hi : i = 0
    · subst i
      have hd : (g.val.val : Mat (q.Extension 2) (s + 2)) 0 0 = 1 := g.property.1.2 0
      simp [Matrix.col, hd]
    · have hb : (g.val.val : Mat (q.Extension 2) (s + 2)) i 0 = 0 :=
        g.property.1.1 (show (0 : Fin (s + 3)) < i from Fin.pos_iff_ne_zero.mpr hi)
      simp [Matrix.col, hb, Pi.single_apply, hi]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical
