import SymmetricSubgroupAsymptotics.BinaryEightTop31StableFilter
import SymmetricSubgroupAsymptotics.BinaryEightTop31K26Head
import SymmetricSubgroupAsymptotics.BinaryEightTop31K29Head
import SymmetricSubgroupAsymptotics.BinaryEightTop31K31Head
import SymmetricSubgroupAsymptotics.BinaryEightTop31K37Head
import SymmetricSubgroupAsymptotics.BinaryEightTop31RegularSparse
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.RepresentationRestrictionSameVectors
import SymmetricSubgroupAsymptotics.BinaryPermutationSubgroupRestriction

/-! Exact two possible head-two correlated kernels under the original31
action. Completeness comes from its actual regularE8 subgroup and the
already checked47-space registry, followed by actual31 stability/heads. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31HighHeadKernel
open BinaryEightTop31CoordinateAction
abbrev inclusion : BinaryRegularEightNaturalRegistry.H →* H :=
  Subgroup.inclusion BinaryEightTop31RegularSparse.regular_le

private theorem restriction_action_eq (t : BinaryRegularEightNaturalRegistry.H) (v : V) :
    rho (inclusion t) v = BinaryRegularEightNaturalRegistry.rho t v :=
  binaryPermutation_subgroup_restriction BinaryRegularEightNaturalRegistry.H H
    BinaryEightTop31RegularSparse.regular_le t v

def regularRestriction (W : Subrepresentation rho) :
    Subrepresentation BinaryRegularEightNaturalRegistry.rho :=
  restrictionSameVectors rho BinaryRegularEightNaturalRegistry.rho inclusion restriction_action_eq W

theorem regularRestriction_space (W : Subrepresentation rho) :
    (regularRestriction W).toSubmodule = W.toSubmodule :=
  restrictionSameVectors_space rho BinaryRegularEightNaturalRegistry.rho inclusion restriction_action_eq W

theorem head_le_regular (W : Subrepresentation rho) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
      Module.finrank (ZMod 2) (regularRestriction W).toRepresentation.Coinvariants :=
  restrictionSameVectors_head_le rho BinaryRegularEightNaturalRegistry.rho inclusion restriction_action_eq W

theorem high_head_space (W : Subrepresentation rho)
    (hhigh : 1 < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    W.toSubmodule = BinaryRegularEightNaturalRegistry.chart44.space ∨
      W.toSubmodule = BinaryRegularEightNaturalRegistry.chart45.space := by
  obtain ⟨i,hi⟩ := BinaryRegularEightNaturalRegistry.complete (regularRestriction W)
  have hrestrict := regularRestriction_space W
  have hspace : W.toSubmodule = (BinaryRegularEightNaturalRegistry.charts i).2.space :=
    hrestrict.symm.trans ((congrArg Subrepresentation.toSubmodule hi.symm).trans
      (BinaryRegularEightNaturalRegistry.states_space i))
  have hlow : BinaryRegularEightNaturalRegistry.headCeiling i ≤ 1 → False := by
    intro hb
    have hr := head_le_regular W
    rw [← hi] at hr
    have hh := (BinaryRegularEightNaturalRegistry.coinvariants_finrank_le i).trans hb
    omega
  have hs := BinaryEightTop31StableFilter.stable_of_actual_space W i hspace
  rcases BinaryEightTop31StableFilter.stable_index i hs with
    h|h|h|h|h|h|h|h|h|h|h|h|h
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i
    have hh := BinaryEightTop31K26Head.head_le_one W hspace
    omega
  · subst i
    have hh := BinaryEightTop31K29Head.head_le_one W hspace
    omega
  · subst i
    have hh := BinaryEightTop31K31Head.head_le_one W hspace
    omega
  · subst i
    have hh := BinaryEightTop31K37Head.head_le_one W hspace
    omega
  · subst i; exact Or.inl hspace
  · subst i; exact Or.inr hspace
end SymmetricSubgroupAsymptotics.BinaryEightTop31HighHeadKernel
