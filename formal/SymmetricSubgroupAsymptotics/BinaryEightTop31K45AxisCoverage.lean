import SymmetricSubgroupAsymptotics.BinaryEightTop31HighHeadKernel
import SymmetricSubgroupAsymptotics.BinaryEightTop31K45JointCounts

/-! Every original normal-axis inside the augmentation kernel is one of
twelve retained spaces. Actual31 invariance and the existing regularE8
coverage prove this; no original normal-subgroup census is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31K45AxisCoverage
open BinaryEightTop31CoordinateAction BinaryEightTop31K45JointCounts
private theorem full_not_le :
    ¬ BinaryRegularEightNaturalRegistry.chart1.space ≤ BinaryRegularEightNaturalRegistry.chart45.space := by
  intro h
  have hn : BinaryRegularEightNaturalRegistry.chart1.inclusion (Pi.single (0 : Fin 8) 1) ∉
      BinaryRegularEightNaturalRegistry.chart45.space := by decide +kernel
  exact hn (h ⟨_,rfl⟩)

theorem complete (W : Subrepresentation rho)
    (hW : W.toSubmodule ≤ BinaryRegularEightNaturalRegistry.chart45.space) :
    ∃ i : Fin 12, W.toSubmodule = (axes i).2.space := by
  obtain ⟨i,hi⟩ := BinaryRegularEightNaturalRegistry.complete
    (BinaryEightTop31HighHeadKernel.regularRestriction W)
  have hs : W.toSubmodule = (BinaryRegularEightNaturalRegistry.charts i).2.space :=
    (BinaryEightTop31HighHeadKernel.regularRestriction_space W).symm.trans
      ((congrArg Subrepresentation.toSubmodule hi.symm).trans
        (BinaryRegularEightNaturalRegistry.states_space i))
  have hstable := BinaryEightTop31StableFilter.stable_of_actual_space W i hs
  rcases BinaryEightTop31StableFilter.stable_index i hstable with
    h|h|h|h|h|h|h|h|h|h|h|h|h
  · subst i; exact ⟨0,hs⟩
  · subst i
    have hh : BinaryRegularEightNaturalRegistry.chart1.space ≤
        BinaryRegularEightNaturalRegistry.chart45.space := hs ▸ hW
    exact (full_not_le hh).elim
  · subst i; exact ⟨1,hs⟩
  · subst i; exact ⟨2,hs⟩
  · subst i; exact ⟨3,hs⟩
  · subst i; exact ⟨4,hs⟩
  · subst i; exact ⟨5,hs⟩
  · subst i; exact ⟨6,hs⟩
  · subst i; exact ⟨7,hs⟩
  · subst i; exact ⟨8,hs⟩
  · subst i; exact ⟨9,hs⟩
  · subst i; exact ⟨10,hs⟩
  · subst i; exact ⟨11,hs⟩
end SymmetricSubgroupAsymptotics.BinaryEightTop31K45AxisCoverage
