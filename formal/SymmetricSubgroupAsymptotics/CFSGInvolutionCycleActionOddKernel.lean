import SymmetricSubgroupAsymptotics.CFSGInvolutionCentralizerTwoKernel
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Every nonidentity involution has an actual odd element in the kernel
of its centralizer's cycle action: any one of its literal two-cycles. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGInvolutionCycleActionOddKernel
open Equiv Perm

theorem exists_odd_kernel {X : Type*} [Fintype X] [DecidableEq X]
    (t : Perm X) (ht : t ^ 2 = 1) (hne : t ≠ 1) :
    ∃ c : Subgroup.centralizer ({t} : Set (Perm X)),
      c ∈ (OnCycleFactors.toPermHom t).ker ∧ c.val ∉ alternatingGroup X := by
  have hnonempty : t.cycleFactorsFinset.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hne (cycleFactorsFinset_eq_empty_iff.mp h))
  obtain ⟨c, hc⟩ := hnonempty
  have hcC : c ∈ Subgroup.centralizer ({t} : Set (Perm X)) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    have he : y = t := Set.mem_singleton_iff.mp hy
    subst y
    exact (self_mem_cycle_factors_commute hc).symm.eq
  refine ⟨⟨c, hcC⟩, ?_, ?_⟩
  · apply (OnCycleFactors.mem_ker_toPermHom_iff t ⟨c, hcC⟩).mpr
    intro d hd
    exact cycleFactorsFinset_mem_commute' t hc hd
  · intro he
    have hs := (mem_cycleFactorsFinset_iff.mp hc).1.sign
    rw [CFSGInvolutionCentralizerTwoKernel.cycle_support_card_eq_two t ht ⟨c, hc⟩] at hs
    have h1 := mem_alternatingGroup.mp he
    rw [h1] at hs
    norm_num at hs

end SymmetricSubgroupAsymptotics.CFSGInvolutionCycleActionOddKernel
