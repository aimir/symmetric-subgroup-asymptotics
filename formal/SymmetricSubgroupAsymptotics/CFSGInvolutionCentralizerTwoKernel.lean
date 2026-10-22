import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.PGroup

/-! The literal cycle action of the centralizer of an involution.
All nontrivial cycles have length two, so the action on its cycles is
onto the full symmetric group. If at most one point is fixed, the kernel
is a two-group. These facts use Mathlib's actual centralizer maps. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGInvolutionCentralizerTwoKernel
open Equiv Equiv.Perm
variable {X : Type*} [Fintype X] [DecidableEq X] (t : Perm X) (ht : t ^ 2 = 1)
include ht

theorem cycle_support_card_eq_two (c : t.cycleFactorsFinset) : c.val.support.card = 2 := by
  have hm : c.val.support.card ∈ t.cycleType := by
    rw [cycleType_def]
    exact Multiset.mem_map.mpr ⟨c.val, c.property, rfl⟩
  have hlo := two_le_of_mem_cycleType hm
  have hd := (dvd_of_mem_cycleType hm).trans (orderOf_dvd_of_pow_eq_one ht)
  exact Nat.le_antisymm (Nat.le_of_dvd (by decide : 0 < 2) hd) hlo

theorem cycleAction_surjective : Function.Surjective (OnCycleFactors.toPermHom t) := by
  intro tau
  apply OnCycleFactors.mem_range_toPermHom_iff.mpr
  intro c
  rw [cycle_support_card_eq_two t ht (tau c), cycle_support_card_eq_two t ht c]

theorem cycleAction_kernel_isPGroup
    (hfix : {x : X | t x = x}.Subsingleton) :
    IsPGroup 2 (OnCycleFactors.toPermHom t).ker := by
  letI : Subsingleton (Function.fixedPoints t) :=
    ⟨fun a b => Subtype.ext (hfix a.property b.property)⟩
  let D := (Perm (Function.fixedPoints t)) ×
    ((c : t.cycleFactorsFinset) → Subgroup.zpowers c.val)
  have hD : IsPGroup 2 D := by
    intro g
    refine ⟨1, ?_⟩
    change g ^ 2 = 1
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext c
      apply Subtype.ext
      change (g.2 c).val ^ 2 = 1
      apply orderOf_dvd_iff_pow_eq_one.mp
      have hd := orderOf_dvd_of_mem_zpowers (g.2 c).property
      have hc := (mem_cycleFactorsFinset_iff.mp c.property).1.orderOf
      rw [hc, cycle_support_card_eq_two t ht c] at hd
      exact hd
  have hR : IsPGroup 2 (OnCycleFactors.kerParam t).range :=
    hD.of_surjective (OnCycleFactors.kerParam t).rangeRestrict
      (OnCycleFactors.kerParam t).rangeRestrict_surjective
  have hC := hR.comap_of_injective (Subgroup.centralizer ({t} : Set (Perm X))).subtype
    (Subgroup.centralizer ({t} : Set (Perm X))).subtype_injective
  apply hC.to_le
  intro g hg
  change (g.val : Perm X) ∈ (OnCycleFactors.kerParam t).range
  rw [OnCycleFactors.kerParam_range_eq]
  exact ⟨g, hg, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGInvolutionCentralizerTwoKernel
