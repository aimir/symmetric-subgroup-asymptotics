import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootAxisPairing
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalColumnClearing

/-! The checked literal radical clears every signed-isotropic vector
with nonzero last coordinate, not only a column of an existing matrix.
This supplies actual point coverage without a full-unitary premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryUpperArrays CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedAUnitaryParameters CFSGTwistedAUnitaryColumnClearing CFSGSerreOrdinaryTwists

theorem upper_clear_isotropic_vector (q : CFSG.PrimePower) (s : ℕ)
    (x : Fin (s + 3) → q.Extension 2)
    (hx : unitaryNaturalPair q (s + 2) x x = 0) (hb : x (Fin.last (s + 2)) ≠ 0) :
    ∃ u : naturalUnipotent (s + 2) q,
      (u.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x =
        Pi.single (Fin.last (s + 2)) (x (Fin.last (s + 2))) := by
  let y : Index (Fin (s + 1)) → q.Extension 2 := x ∘ splitEquiv s
  have hnorm := hermitianPair_reindex (definingFieldAutomorphism q 2) (splitEquiv s)
    (blockForm (parity q s) (middleForm q s)) x x
  have hblock : Matrix.reindex (splitEquiv s) (splitEquiv s)
      (blockForm (parity q s) (middleForm q s)) =
        (signedReversalUnit (q.Extension 2) (s + 2) : Mat (q.Extension 2) (s + 2)) :=
    blockForm_reindex (q.Extension 2) s
  rw [hblock] at hnorm
  have hiso : definingFieldAutomorphism q 2 (y (.inl ())) * y (.inr (.inr ())) +
      hermitianNorm (definingFieldAutomorphism q 2) (middleForm q s) (fun i => y (.inr (.inl i))) +
        parity q s * definingFieldAutomorphism q 2 (y (.inr (.inr ()))) * y (.inl ()) = 0 := by
    rw [← blockForm_quadratic]
    exact hnorm.symm.trans hx
  obtain ⟨v, c, hc, hclear⟩ := upper_clear_column (definingFieldAutomorphism q 2)
    (fun a => extension_two_pow_twice q a) (parity q s)
    (neg_one_pow_eq_or (q.Extension 2) s) (middleForm q s) y hb hiso
  have hc' : Condition q s v c := hc
  refine ⟨radicalElement q s v c hc', ?_⟩
  funext i
  obtain ⟨p, rfl⟩ := (splitEquiv s).surjective i
  rw [radicalElement_matrix, reindex_mulVec_apply]
  change (upperArray (radicalRow (definingFieldAutomorphism q 2) (parity q s) (middleForm q s) v) v c *ᵥ y) p = _
  rw [hclear]
  have hl : splitEquiv s (.inr (.inr ())) = Fin.last (s + 2) := rfl
  have hlast : y (.inr (.inr ())) = x (Fin.last (s + 2)) := rfl
  simp only [hlast, ← hl, Pi.single_apply, (splitEquiv s).injective.eq_iff]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
