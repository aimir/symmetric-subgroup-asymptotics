import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryDerivedCentralScalar
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! The literal natural fixed group covers the ORIGINAL projective
derived source, and its kernel consists exactly of scalar matrices.
This follows from the proved central-lift theorem and the actual adjoint
action kernel; no projective-model recognition is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAIntervalSource

theorem scalar_naturalFixedToOriginal_eq_one (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q)
    (hscalar : ∃ c : q.Extension 2, (g.val.val : Mat (q.Extension 2) (s + 3)) = c • 1) :
    naturalFixedToOriginal q (s + 3) g = 1 := by
  have hk : g.val ∈ (naturalElementaryAction (q.Extension 2) (s + 3)).ker := by
    rw [naturalElementaryAction_ker (q.Extension 2) (s + 3) (by omega)]
    exact (naturalElementary_center_iff_scalar (q.Extension 2) (s + 3) (by omega) g.val).mpr hscalar
  apply twistedFixedAction_injective q (s + 3)
  rw [map_one]
  exact (elementaryToModel_action (q.Extension 2) (s + 3) g.val).trans hk

theorem originalDerived_center_eq_bot (q : CFSG.PrimePower) (s : ℕ) :
    Subgroup.center (commutator (Fixed (s + 3) q)) = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨g, rfl⟩ := originalDerivedCover_surjective q s x
  have hs := central_cover_scalar q s g hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  exact scalar_naturalFixedToOriginal_eq_one q s g hs

def unitaryProjectiveCover (q : CFSG.PrimePower) (s : ℕ) :
    naturalFixed (s + 3) q →* CFSG.Models.TwistedA (s + 3) q :=
  (QuotientGroup.mk' (Subgroup.center (commutator (Fixed (s + 3) q)))).comp
    (originalDerivedCover q s)

theorem unitaryProjectiveCover_surjective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Surjective (unitaryProjectiveCover q s) :=
  (QuotientGroup.mk'_surjective _).comp (originalDerivedCover_surjective q s)

theorem unitaryProjectiveCover_kernel_iff_scalar (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) :
    unitaryProjectiveCover q s g = 1 ↔
      ∃ c : q.Extension 2, (g.val.val : Mat (q.Extension 2) (s + 3)) = c • 1 := by
  constructor
  · intro h
    have hc : originalDerivedCover q s g ∈ Subgroup.center (commutator (Fixed (s + 3) q)) :=
      (QuotientGroup.eq_one_iff _).mp h
    exact central_cover_scalar q s g hc
  · intro h
    have hg : originalDerivedCover q s g = 1 :=
      Subtype.ext (scalar_naturalFixedToOriginal_eq_one q s g h)
    change QuotientGroup.mk' _ (originalDerivedCover q s g) = 1
    rw [hg, map_one]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
