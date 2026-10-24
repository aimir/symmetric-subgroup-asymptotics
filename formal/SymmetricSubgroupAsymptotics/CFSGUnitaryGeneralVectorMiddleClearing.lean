import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalFixedSpace

/-! An actual determinant-one unitary radical clears the middle of an
arbitrary vector with nonzero last coordinate. The vector is not assumed
singular, so its remaining first coordinate is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUnitaryNaturalRadical

theorem exists_radical_array_clear_middle (q : CFSG.PrimePower) (s : ℕ)
    (x : Index (Fin (s + 1)) → q.Extension 2)
    (hx : x (.inr (.inr ())) ≠ 0) :
    ∃ (v : Fin (s + 1) → q.Extension 2) (b : q.Extension 2) (hb : Condition q s v b)
      (a : q.Extension 2),
      upperArray (firstRow q s v) v b *ᵥ x =
        Pi.single (.inl ()) a + Pi.single (.inr (.inr ())) (x (.inr (.inr ()))) := by
  let v : Fin (s + 1) → q.Extension 2 := fun i => -x (.inr (.inl i)) / x (.inr (.inr ()))
  obtain ⟨b, hb⟩ := condition_exists q s v
  let a := (upperArray (firstRow q s v) v b *ᵥ x) (.inl ())
  refine ⟨v, b, hb, a, ?_⟩
  ext p
  rcases p with u | (i | u)
  · cases u
    simp only [Pi.add_apply, Pi.single_apply, ite_true, reduceCtorEq, ite_false, add_zero]
    rfl
  · simp only [Pi.add_apply, Pi.single_apply, Sum.inr.injEq, reduceCtorEq, ite_false, zero_add]
    rw [upperArray_mulVec_middle]
    change x (.inr (.inl i)) + (-x (.inr (.inl i)) / x (.inr (.inr ()))) *
      x (.inr (.inr ())) = 0
    rw [div_mul_cancel₀ _ hx, add_neg_cancel]
  · cases u
    simp only [Pi.add_apply, Pi.single_apply, reduceCtorEq, ite_false, ite_true, zero_add]
    exact upperArray_mulVec_last _ _ _ _

theorem exists_natural_radical_clear_middle (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 3) → q.Extension 2) (hx : x (Fin.last (s + 2)) ≠ 0) :
    ∃ (u : CFSGTwistedAUpperUnipotent.naturalUnipotent (s + 2) q) (a : q.Extension 2),
      ((u.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x) =
        Pi.single 0 a + Pi.single (Fin.last (s + 2)) (x (Fin.last (s + 2))) := by
  let y : Index (Fin (s + 1)) → q.Extension 2 := x ∘ splitEquiv s
  have hy : y (.inr (.inr ())) ≠ 0 := hx
  obtain ⟨v, b, hb, a, hclear⟩ := exists_radical_array_clear_middle q s y hy
  refine ⟨radicalElement q s v b hb, a, ?_⟩
  funext i
  obtain ⟨p, rfl⟩ := (splitEquiv s).surjective i
  rw [radicalElement_matrix, reindex_mulVec_apply]
  change (upperArray (firstRow q s v) v b *ᵥ y) p = _
  rw [hclear]
  have hfirst : splitEquiv s (.inl ()) = 0 := rfl
  have hlast : splitEquiv s (.inr (.inr ())) = Fin.last (s + 2) := rfl
  simp only [Pi.add_apply, ← hfirst, ← hlast, Pi.single_apply,
    (splitEquiv s).injective.eq_iff]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
