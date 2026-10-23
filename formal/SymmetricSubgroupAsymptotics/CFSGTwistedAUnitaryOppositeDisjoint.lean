import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOriginalGeneration
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowerOpposite

/-! Literal opposite upper subgroups have trivial intersection, first
on the natural matrices and then in the original defining-fixed source.
The second step uses the proved scalar separation for actual p-elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGTwistedAIntervalSource

theorem upper_eq_one_of_mem_opposite (q : CFSG.PrimePower) (r : ℕ)
    (u : naturalUnipotent r q) (hu : u.val ∈ oppositeNaturalUnipotent q r) : u = 1 := by
  obtain ⟨v, hv, he⟩ := hu
  have hlower (i j : Fin (r + 1)) (hij : i < j) :
      (u.val.val : Mat (q.Extension 2) r) i j = 0 := by
    have hh := congrArg (fun z : NaturalElementary (q.Extension 2) r =>
      (z.val : Mat (q.Extension 2) r) i j) he
    change ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *
      (v.val : Mat (q.Extension 2) r) *
        (↑((signedReversalUnit (q.Extension 2) r)⁻¹) : Mat (q.Extension 2) r)) i j = _ at hh
    have hz : (v.val : Mat (q.Extension 2) r) i.rev j.rev = 0 :=
      hv.1.1 (Fin.rev_lt_rev.mpr hij)
    rw [signedReversal_conjugation_entry, hz, mul_zero, zero_mul] at hh
    exact hh.symm
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (u.val.val : Mat (q.Extension 2) r) i j = (1 : Mat (q.Extension 2) r) i j
  by_cases heq : i = j
  · subst j
    exact (u.property.1.2 i).trans (Matrix.one_apply_eq i).symm
  · rw [Matrix.one_apply, if_neg heq]
    rcases lt_or_gt_of_ne heq with hij | hji
    · exact hlower i j hij
    · exact u.property.1.1 hji

theorem original_upper_inf_opposite (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    originalUnipotent r q ⊓ originalOppositeUnipotent q r = ⊥ := by
  apply bot_unique
  rintro x ⟨hx, hy⟩
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨_, ⟨v, rfl⟩, he⟩ := hy
  have hw : twistedFixedAction r q (originalReversal q r) =
      naturalElementaryAction (q.Extension 2) r (reversalNatural q r) :=
    elementaryToModel_action (q.Extension 2) r (reversalNatural q r)
  have ha := congrArg (twistedFixedAction r q) he
  change twistedFixedAction r q
    (originalReversal q r * unipotentToOriginalFixed r q v * (originalReversal q r)⁻¹) =
      twistedFixedAction r q (unipotentToOriginalFixed r q u) at ha
  simp only [map_mul, map_inv, unipotentToOriginalFixed_action, hw] at ha
  have hn : reversalNatural q r * v.val * (reversalNatural q r)⁻¹ = u.val :=
    upper_conjugate_of_action_eq q r hr _ v u (by
      simpa only [map_mul, map_inv] using ha)
  have hu : u = 1 := upper_eq_one_of_mem_opposite q r u ⟨v.val, v.property, hn⟩
  simp only [hu, map_one, Subgroup.mem_bot]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
