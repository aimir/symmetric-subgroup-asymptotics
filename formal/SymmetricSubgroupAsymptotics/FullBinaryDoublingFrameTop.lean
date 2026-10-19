import SymmetricSubgroupAsymptotics.FullBinaryDoubling
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! ANY invariant pair frame on the full binary doubling recovers the
original top as an actual group. Thus an existential frame in a published
catalogue realization cannot silently change the original action group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FullBinaryDoubling
variable {I : Type} (U : Subgroup (Equiv.Perm I))
  (R : BinaryPairFrame (group U) I)

private theorem binary_cases : ∀ b : ZMod 2,b=0 ∨ b=1 := by decide +kernel
private theorem binary_equal_or_other : ∀ a b : ZMod 2,a=b ∨ b=a+1 := by decide +kernel

def label (j : I) : I := (R.frame (j,0)).1

theorem frame_label (j : I) (b : ZMod 2) : (R.frame (j,b)).1=label U R j := by
  rcases binary_cases b with h0 | h1
  · subst b
    rfl
  · subst b
    have hp := every_frame_partner U R (R.frame (j,0))
    rw [R.partnerMap_frame] at hp
    simpa only [zero_add,label] using
      congrArg (fun z : I × ZMod 2 => z.1) hp

theorem label_injective : Function.Injective (label U R) := by
  intro j k h
  have hf : (R.frame (j,0)).1=(R.frame (k,0)).1 := h
  rcases binary_equal_or_other (R.frame (j,0)).2 (R.frame (k,0)).2 with he | he
  · exact congrArg Prod.fst (R.frame.injective (Prod.ext hf he))
  · have hp : R.frame (k,0)=R.partnerMap (R.frame (j,0)) := by
      rw [every_frame_partner U R]
      exact Prod.ext hf.symm he
    rw [R.partnerMap_frame] at hp
    exact (congrArg Prod.fst (R.frame.injective hp)).symm

def labelEquiv [Finite I] : I ≃ I :=
  Equiv.ofBijective (label U R)
    ⟨label_injective U R,Finite.surjective_of_injective (label_injective U R)⟩

/-- Actual conjugation of label actions, with no module-field transport. -/
theorem top_label (g : group U) (j : I) :
    label U R (R.top g j)=(topHom U g : Equiv.Perm I) (label U R j) := by
  let x := g.val (R.frame (j,0))
  have hx := frame_label U R (R.frame.symm x).1 (R.frame.symm x).2
  rw [R.frame.apply_symm_apply] at hx
  have hi := R.intertwine g (j,0)
  change (R.frame.symm x).1=R.top g j at hi
  rw [hi] at hx
  exact hx.symm.trans (top_spec U g (R.frame (j,0)))

theorem frame_top_kernel [Finite I] : R.top.rangeRestrict.ker=(topHom U).ker := by
  ext g
  constructor
  · intro hg
    change R.top.rangeRestrict g=1 at hg
    have hr : R.top g=1 := congrArg (fun a : R.top.range => (a : Equiv.Perm I)) hg
    change topHom U g=1
    apply Subtype.ext
    apply Equiv.ext
    intro i
    let e := labelEquiv U R
    have h := top_label U R g (e.symm i)
    rw [hr] at h
    have he : label U R (e.symm i)=i := e.apply_symm_apply i
    simpa only [Equiv.Perm.one_apply,he] using h.symm
  · intro hg
    change topHom U g=1 at hg
    change R.top.rangeRestrict g=1
    apply Subtype.ext
    apply Equiv.ext
    intro j
    apply label_injective U R
    have h := top_label U R g j
    rw [hg] at h
    exact h

/-- The original top is recovered for every returned frame. -/
def frameTopEquiv [Finite I] : R.top.range ≃* U :=
  (QuotientGroup.liftEquiv R.top.rangeRestrict.ker R.top.rangeRestrict_surjective rfl).symm.trans
    (QuotientGroup.liftEquiv R.top.rangeRestrict.ker (top_surjective U) (frame_top_kernel U R))

end SymmetricSubgroupAsymptotics.FullBinaryDoubling
