import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Every central class modulo N lifts to a central class modulo N∩G′.
Thus quotient-centre estimates only need the actual derived-denominator
lattice; no enumeration of all normal subgroups is required. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G]

theorem quotient_center_lift_through_derived_intersection
    (N : Subgroup G) [N.Normal] (z : Subgroup.center (G ⧸ N)) :
    ∃ g : G,(QuotientGroup.mk' N) g=(z : G ⧸ N) ∧
      (QuotientGroup.mk' (N ⊓ commutator G)) g∈
        Subgroup.center (G ⧸ (N ⊓ commutator G)) := by
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective N (z : G ⧸ N)
  refine ⟨g,hg,Subgroup.mem_center_iff.mpr ?_⟩
  intro x
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (N ⊓ commutator G) x
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hcN : ⁅k,g⁆∈N := by
    apply (QuotientGroup.eq_one_iff ⁅k,g⁆).mp
    change (QuotientGroup.mk' N) ⁅k,g⁆=1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    rw [hg]
    exact Subgroup.mem_center_iff.mp z.property _
  have hcD : ⁅k,g⁆∈commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top k) (Subgroup.mem_top g)
  have hh : (QuotientGroup.mk' (N ⊓ commutator G)) ⁅k,g⁆=1 :=
    (QuotientGroup.eq_one_iff ⁅k,g⁆).mpr ⟨hcN,hcD⟩
  simpa only [map_commutatorElement] using hh

/-- The original quotient centre is paid by the centre above the SAME
intersection with the original derived subgroup. -/
theorem quotient_center_card_le_derived_intersection [Finite G]
    (N : Subgroup G) [N.Normal] :
    Nat.card (Subgroup.center (G ⧸ N))≤
      Nat.card (Subgroup.center (G ⧸ (N ⊓ commutator G))) := by
  let M := N ⊓ commutator G
  let q : G ⧸ M →* G ⧸ N := QuotientGroup.lift M (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk']
    exact inf_le_left)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective N x
    exact ⟨(QuotientGroup.mk' M) g,hg⟩
  letI : Finite (G ⧸ M) := Finite.of_surjective
    (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
  have hcentral (z : Subgroup.center (G ⧸ M)) : q z∈Subgroup.center (G ⧸ N) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    obtain ⟨y,rfl⟩ := hq x
    simpa only [map_mul] using congrArg q (Subgroup.mem_center_iff.mp z.property y)
  let f : Subgroup.center (G ⧸ M) → Subgroup.center (G ⧸ N) :=
    fun z => ⟨q z,hcentral z⟩
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨g,hg,hc⟩ := quotient_center_lift_through_derived_intersection N z
    refine ⟨⟨(QuotientGroup.mk' M) g,hc⟩,Subtype.ext ?_⟩
    exact hg
  exact Nat.card_le_card_of_surjective f hf

end SymmetricSubgroupAsymptotics
