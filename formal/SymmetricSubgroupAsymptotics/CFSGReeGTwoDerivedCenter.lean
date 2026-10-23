import SymmetricSubgroupAsymptotics.CFSGReeGTwoBorelCore
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! The actual full centre of the derived original Ree fixed group is
trivial. Its characteristic image is a normal subgroup of the fixed
group; centralizing U places that image in the actual Borel, whose normal
core was proved trivial. No full-fixed-group perfectness is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedCenter
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoOriginalBorel
open CFSGReeGTwoPositiveDerived CFSGReeGTwoFixedRankOneGeometry CFSGReeGTwoBorelCore

theorem derived_center_eq_bot (m : ℕ) (hm : 1≤m) :
    Subgroup.center (commutator (originalModelFixed m))=⊥ := by
  let D := commutator (originalModelFixed m)
  let C : Subgroup (originalModelFixed m) := (Subgroup.center D).map D.subtype
  letI : C.Normal := inferInstance
  have hCB : C≤borelGroup m := by
    rintro _ ⟨z,hz,rfl⟩
    rw [←fixed_positive_normalizer_eq_borel]
    apply (Subgroup.centralizer_le_normalizer
      (fixedPositiveGroup m:Set (originalModelFixed m)))
    apply Subgroup.mem_centralizer_iff.mpr
    intro u hu
    let d : D := ⟨u,fixedPositiveGroup_le_commutator m hm hu⟩
    have he : d*z=z*d := (Subgroup.mem_center_iff.mp hz) d
    exact congrArg (fun x : D=>x.val) he
  have hC := normal_le_borel_eq_bot m C hCB
  apply bot_unique
  intro z hz
  have hmem : z.val∈C := ⟨z,hz,rfl⟩
  rw [hC] at hmem
  apply Subgroup.mem_bot.mpr
  exact Subtype.ext (show z.val=1 from hmem)

def originalReeEquivDerived (m : ℕ) (hm : 1≤m) :
    CFSG.Models.ReeG2 m≃*commutator (originalModelFixed m) :=
  (originalReeEquiv m).trans
    ((QuotientGroup.quotientMulEquivOfEq (derived_center_eq_bot m hm)).trans
      QuotientGroup.quotientBot)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedCenter
