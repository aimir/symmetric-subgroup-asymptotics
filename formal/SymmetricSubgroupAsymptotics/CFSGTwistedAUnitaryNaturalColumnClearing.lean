import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryColumnClearing
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadicalSupport
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalFixedSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalKernel

/-! Genuine first-column elimination for the SAME natural defining-fixed
group, all ranks s+2 and all prime powers. Its isometry equation supplies
the needed isotropy and the resulting clearing element is the actual
literal upper subgroup. No supplied form or generation hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryUpperArrays CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedAUnitaryColumnClearing CFSGSerreOrdinaryTwists

theorem upper_clear_natural_column (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q)
    (hb : (g.val.val : Mat (q.Extension 2) (s + 2)) (Fin.last (s + 2)) 0 ≠ 0) :
    ∃ u : naturalUnipotent (s + 2) q,
      (fun i => ((u.val.val : Mat (q.Extension 2) (s + 2)) *
        (g.val.val : Mat (q.Extension 2) (s + 2))) i 0) =
        Pi.single (Fin.last (s + 2))
          ((g.val.val : Mat (q.Extension 2) (s + 2)) (Fin.last (s + 2)) 0) := by
  let B := blockFixedMatrixHom q s g
  let x : Index (Fin (s + 1)) → q.Extension 2 :=
    fun i => (B : Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) i (.inl ())
  have hx : x = (fun i => (g.val.val : Mat (q.Extension 2) (s + 2)) i 0) ∘ splitEquiv s := by
    funext i
    exact blockFixedMatrixHom_apply q s g i (.inl ())
  have hblast : x (.inr (.inr ())) ≠ 0 := by
    rw [hx]
    exact hb
  have hform := blockFixedMatrixHom_isometry q s g
  have hiso := block_isometry_column_isotropic (definingFieldAutomorphism q 2)
    (parity q s) (middleForm q s)
    (B : Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2)) hform
  obtain ⟨v, c, hc, hclear⟩ := upper_clear_column (definingFieldAutomorphism q 2)
    (fun a => extension_two_pow_twice q a) (parity q s)
    (neg_one_pow_eq_or (q.Extension 2) s) (middleForm q s) x hblast hiso
  have hc' : Condition q s v c := hc
  refine ⟨radicalElement q s v c hc', ?_⟩
  funext i
  obtain ⟨p, rfl⟩ := (splitEquiv s).surjective i
  change (((radicalElement q s v c hc').val.val : Mat (q.Extension 2) (s + 2)) *ᵥ
      (fun j => (g.val.val : Mat (q.Extension 2) (s + 2)) j 0)) (splitEquiv s p) = _
  rw [radicalElement_matrix, reindex_mulVec_apply, ← hx]
  change (upperArray (radicalRow (definingFieldAutomorphism q 2) (parity q s) (middleForm q s) v) v c *ᵥ x) p = _
  rw [hclear]
  have hl : splitEquiv s (.inr (.inr ())) = Fin.last (s + 2) := rfl
  have hbval : x (.inr (.inr ())) =
      (g.val.val : Mat (q.Extension 2) (s + 2)) (Fin.last (s + 2)) 0 := by
    rw [hx]
    rfl
  simp only [hbval, ← hl, Pi.single_apply, (splitEquiv s).injective.eq_iff]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
