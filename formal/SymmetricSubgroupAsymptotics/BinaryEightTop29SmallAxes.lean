import SymmetricSubgroupAsymptotics.BinaryEightTop29HighHeadKernel

/-! Only three original8T29-stable axes have order less than eight.
This is a consequence of existing47-space coverage and the proved
larger-top stability filter, not a normal-subgroup census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightTop29SmallAxes
open BinaryEightTop29CoordinateAction
open BinaryRegularEightNaturalRegistry

theorem small_space (W : Subrepresentation BinaryEightTop29CoordinateAction.rho)
    (hsmall : Nat.card W.toSubmodule < 8) :
    W.toSubmodule = chart0.space ∨ W.toSubmodule = chart22.space ∨
      W.toSubmodule = chart23.space := by
  obtain ⟨i, hi⟩ := complete (BinaryEightTop29HighHeadKernel.regularRestriction W)
  have hspace : W.toSubmodule = (charts i).2.space :=
    (congrArg Subrepresentation.toSubmodule hi.symm).trans (states_space i)
  have hstable := BinaryEightTop29StableFilter.stable_of_actual_space W i hspace
  rcases BinaryEightTop29StableFilter.stable_index i hstable with
    h | h | h | h | h | h | h | h | h | h | h
  · subst i; exact Or.inl hspace
  · subst i; change W.toSubmodule = chart1.space at hspace
    rw [hspace,chart1.card] at hsmall; norm_num at hsmall
  · subst i; change W.toSubmodule = chart3.space at hspace
    rw [hspace,chart3.card] at hsmall; norm_num at hsmall
  · subst i; change W.toSubmodule = chart11.space at hspace
    rw [hspace,chart11.card] at hsmall; norm_num at hsmall
  · subst i; exact Or.inr (Or.inl hspace)
  · subst i; exact Or.inr (Or.inr hspace)
  · subst i; change W.toSubmodule = chart24.space at hspace
    rw [hspace,chart24.card] at hsmall; norm_num at hsmall
  · subst i; change W.toSubmodule = chart30.space at hspace
    rw [hspace,chart30.card] at hsmall; norm_num at hsmall
  · subst i; change W.toSubmodule = chart42.space at hspace
    rw [hspace,chart42.card] at hsmall; norm_num at hsmall
  · subst i; change W.toSubmodule = chart45.space at hspace
    rw [hspace,chart45.card] at hsmall; norm_num at hsmall
  · subst i; change W.toSubmodule = chart46.space at hspace
    rw [hspace,chart46.card] at hsmall; norm_num at hsmall

end SymmetricSubgroupAsymptotics.BinaryEightTop29SmallAxes
