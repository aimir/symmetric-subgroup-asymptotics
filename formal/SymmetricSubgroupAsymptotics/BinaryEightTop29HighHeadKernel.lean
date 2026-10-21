import SymmetricSubgroupAsymptotics.BinaryEightTop29StableFilter
import SymmetricSubgroupAsymptotics.BinaryEightTop29K24Head
import SymmetricSubgroupAsymptotics.BinaryEightTop29K42Head
import SymmetricSubgroupAsymptotics.BinaryEightTop29K45Head
import SymmetricSubgroupAsymptotics.BinaryEightTop29K46Head
import SymmetricSubgroupAsymptotics.BinaryEightRegularTopCoverDirect
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantRestrictionBound

/-! The unique head-two state for the SAME original8T29 action, derived
by restricting to its actual E8 subgroup and filtering the checked47
spaces. No larger-top invariant-registry completeness is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightTop29HighHeadKernel
open BinaryEightTop29CoordinateAction

abbrev inclusion : BinaryRegularEightNaturalRegistry.H →* H :=
  Subgroup.inclusion BinaryEightRegularTopCoverDirect.regular_le_twentyNine

def regularRestriction (W : Subrepresentation rho) :
    Subrepresentation BinaryRegularEightNaturalRegistry.rho where
  toSubmodule := W.toSubmodule
  apply_mem_toSubmodule t v hv := by
    exact W.apply_mem_toSubmodule (inclusion t) hv

theorem head_le_regular (W : Subrepresentation rho) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
      Module.finrank (ZMod 2) (regularRestriction W).toRepresentation.Coinvariants := by
  exact coinvariants_finrank_le_comp_group W.toRepresentation inclusion

theorem high_head_space (W : Subrepresentation rho)
    (hhigh : 1 < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    W.toSubmodule = BinaryRegularEightNaturalRegistry.chart30.space := by
  obtain ⟨i, hi⟩ := BinaryRegularEightNaturalRegistry.complete (regularRestriction W)
  have hspace : W.toSubmodule = (BinaryRegularEightNaturalRegistry.charts i).2.space :=
    (congrArg Subrepresentation.toSubmodule hi.symm).trans
      (BinaryRegularEightNaturalRegistry.states_space i)
  have hlow : BinaryRegularEightNaturalRegistry.headCeiling i ≤ 1 → False := by
    intro hb
    have hr := head_le_regular W
    rw [← hi] at hr
    have hh := (BinaryRegularEightNaturalRegistry.coinvariants_finrank_le i).trans hb
    omega
  have hstable := BinaryEightTop29StableFilter.stable_of_actual_space W i hspace
  rcases BinaryEightTop29StableFilter.stable_index i hstable with
    h | h | h | h | h | h | h | h | h | h | h
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i; exact (hlow (by decide)).elim
  · subst i
    have hh := BinaryEightTop29K24Head.head_le_one W hspace
    omega
  · subst i
    exact hspace
  · subst i
    have hh := BinaryEightTop29K42Head.head_le_one W hspace
    omega
  · subst i
    have hh := BinaryEightTop29K45Head.head_le_one W hspace
    omega
  · subst i
    have hh := BinaryEightTop29K46Head.head_le_one W hspace
    omega

end SymmetricSubgroupAsymptotics.BinaryEightTop29HighHeadKernel
