import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryFixedRadicalGroup
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperIsometryEntries
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralDerived

/-! The actual vector-quotient kernel is killed in the ORIGINAL fixed
source abelianization. Its zero middle parameter forces the first row
zero by the defining signed-form equation, leaving precisely the already
proved central commutator layer. No source-kernel premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent CFSGTwistedAUnitaryNaturalRadical
open CFSGSerreOrdinaryTwists

theorem blockFixedMatrixHom_isometry (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q) :
    ((blockFixedMatrixHom q s g : Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)).map
      (definingFieldAutomorphism q 2)).transpose * blockForm (parity q s) (middleForm q s) *
        (blockFixedMatrixHom q s g : Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) =
      blockForm (parity q s) (middleForm q s) := by
  have hs := fixed_unit_signedForm (q.Extension 2) (s + 2)
    (definingFieldAutomorphism q 2).toRingHom g.val.val g.property
  have h := reindex_isometry (splitEquiv s).symm (definingFieldAutomorphism q 2).toRingHom
    (signedReversalUnit (q.Extension 2) (s + 2) : Mat (q.Extension 2) (s + 2))
    (g.val.val : Mat (q.Extension 2) (s + 2)) hs
  have hf : Matrix.reindex (splitEquiv s).symm (splitEquiv s).symm
      (signedReversalUnit (q.Extension 2) (s + 2) : Mat (q.Extension 2) (s + 2)) =
        blockForm (parity q s) (middleForm q s) := by
    rw [← blockForm_reindex]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Equiv.symm_apply_apply]
    all_goals rfl
  rw [hf] at h
  exact h

theorem fixedRadicalParameter_kernel_original_derived (q : CFSG.PrimePower) (s : ℕ)
    (g : fixedRadical q s) (hg0 : fixedRadicalParameterHom q s g = 1) :
    radicalToOriginal q s g ∈ commutator (Fixed (s + 2) q) := by
  obtain ⟨w, v, b, hg⟩ := g.property
  change Multiplicative.ofAdd (fun i =>
    (blockFixedMatrixHom q s g.val : Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))
      (.inr (.inl i)) (.inr (.inr ()))) = 1 at hg0
  rw [hg] at hg0
  change Multiplicative.ofAdd v = 1 at hg0
  have hv : v = 0 := congrArg Multiplicative.toAdd hg0
  subst v
  have hs := blockFixedMatrixHom_isometry q s g.val
  rw [hg] at hs
  change ((upperArray w 0 b).map (definingFieldAutomorphism q 2)).transpose *
    blockForm (parity q s) (middleForm q s) * upperArray w 0 b =
      blockForm (parity q s) (middleForm q s) at hs
  have hw : w = 0 := by
    funext i
    have hi := upperArray_isometry_left_entry (definingFieldAutomorphism q 2).toRingHom
      (parity q s) (middleForm q s) w 0 b hs i
    apply (definingFieldAutomorphism q 2).injective
    simpa only [Matrix.mulVec_zero, Pi.zero_apply, add_zero, map_zero] using hi
  subst w
  have hb : Condition q s 0 b := by
    apply (centralCondition_iff q s b).mpr
    have hi := upperArray_isometry_central_entry (definingFieldAutomorphism q 2).toRingHom
      (parity q s) (middleForm q s) 0 0 b hs
    simpa only [Matrix.mulVec_zero, dotProduct_zero, add_zero] using hi
  have he : g = fixedRadicalElement q s 0 b hb := by
    apply Subtype.ext
    apply blockFixedMatrixHom_injective q s
    change blockFixedMatrixHom q s g.val = blockFixedMatrixHom q s
      ⟨(radicalElement q s 0 b hb).val, (radicalElement q s 0 b hb).property.2⟩
    rw [blockFixedMatrixHom_radicalElement, firstRow_zero_eq]
    exact hg
  rw [he]
  exact radicalCentral_mem_commutator q s b hb

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
