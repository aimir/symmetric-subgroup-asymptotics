import SymmetricSubgroupAsymptotics.BinaryPlaneLocalCubicTransport
import SymmetricSubgroupAsymptotics.BinaryPlaneInvariantLineFrame
import SymmetricSubgroupAsymptotics.BinaryPlaneCubicOrFixedVector

/-! Honest actual zero-odd dichotomy: either the top is injective, with a
real regular V4 lift available, or the actual linear image preserves a
nonzero line in each quartet. No semantic catalogue case is discarded. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddDichotomy
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (top)
open BinaryPlaneWreathActualOddKernel

def stabilizer (C : Subgroup Frame) : Subgroup C :=
  (MulAction.stabilizer (Equiv.Perm (Fin 4)) (0 : Fin 4)).comap (top C)

def localStabilizer (C : Subgroup Frame) : stabilizer C →* Linear where
  toFun g := ((g : C) : Frame).left 0
  map_one' := rfl
  map_mul' g h := by
    have hg : ((g : C) : Frame).right 0=0 := g.property
    have hi : ((g : C) : Frame).right⁻¹ 0=0 := by
      have he := congrArg ((g : C) : Frame).right.symm hg
      simpa only [Equiv.symm_apply_apply] using he.symm
    change ((((g : C) : Frame)*((h : C) : Frame)).left 0)=_
    rw [PermutationalWreathProduct.mul_left]
    change ((g : C) : Frame).left 0*((h : C) : Frame).left
      (((g : C) : Frame).right⁻¹ 0)=_
    rw [hi]

theorem dichotomy (C : Subgroup Frame) (hzero : oddKernel C=⊥)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    Function.Injective (top C) ∨
      ∃ v : Fin 4 → Plane, (∀ i, v i≠0) ∧
        ∀ (g : C) (i : Fin 4),
          (g : Frame).left ((g : Frame).right i) (v i)=v ((g : Frame).right i) := by
  rcases BinaryPlaneCubicOrFixedVector.dichotomy (localStabilizer C).range with hc | hf
  · left
    obtain ⟨a,ha,han⟩ := hc
    obtain ⟨q,hq⟩ := a.property
    have hqc : (((q : C) : Frame).left 0)^3=1 := by
      have hh : (a : Linear)^3=1 := by
        simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val ha
      rw [← hq] at hh
      exact hh
    have hqn : (((q : C) : Frame).left 0)≠1 := by
      intro h
      apply han
      apply Subtype.ext
      exact hq.symm.trans h
    exact BinaryPlaneLocalCubicTransport.top_injective C hzero heven 0 (q : C)
      q.property hqc hqn
  · right
    obtain ⟨v,hv,hfixed⟩ := hf
    apply BinaryPlaneInvariantLineFrame.exists_frame C heven v hv
    intro s hs
    let q : stabilizer C := ⟨s,hs⟩
    exact hfixed ⟨localStabilizer C q,⟨q,rfl⟩⟩

end SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddDichotomy
