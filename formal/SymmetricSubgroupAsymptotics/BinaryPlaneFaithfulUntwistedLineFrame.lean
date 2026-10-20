import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddDichotomy
import SymmetricSubgroupAsymptotics.AlternatingFourBinaryActualPolynomialUniform

/-! An untwisted faithful quartet top actually preserves local lines.
It belongs to the earlier genuine pair-frame branch on original points. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulUntwistedLineFrame
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (top)
open BinaryPlaneZeroOddDichotomy (stabilizer localStabilizer)
open AlternatingFourBinaryActualPolynomialUniform (cycle)

private theorem stabilizer_cases : ∀ p : Equiv.Perm (Fin 4), p 0=0 →
    p^2=1 ∨ p=cycle ∨ p=cycle^2 := by decide +kernel

theorem exists_frame (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (g : C) (hg : (g : Frame).right=cycle) (hlocal : (g : Frame).left 0=1) :
    ∃ v : Fin 4 → Plane, (∀ i, v i≠0) ∧
      ∀ (q : C) (i : Fin 4),
        (q : Frame).left ((q : Frame).right i) (v i)=v ((q : Frame).right i) := by
  let z : stabilizer C := ⟨g,by
    change (g : Frame).right 0=0
    rw [hg]
    decide +kernel⟩
  have hz : localStabilizer C z=1 := hlocal
  have hsquare : ∀ q : stabilizer C, (localStabilizer C q)^2=1 := by
    intro q
    rcases stabilizer_cases ((q : C) : Frame).right q.property with h | h | h
    · have hq : q^2=1 := Subtype.ext (hinj (by
        simp only [Subgroup.coe_pow,Subgroup.coe_one]
        rw [map_pow,map_one]
        exact h))
      rw [← map_pow,hq,map_one]
    · have hq : q=z := Subtype.ext (hinj (h.trans hg.symm))
      rw [hq,hz,one_pow]
    · have hq : q=z^2 := Subtype.ext (hinj (by
        simp only [Subgroup.coe_pow]
        rw [map_pow]
        change ((q : C) : Frame).right=(g : Frame).right^2
        rw [hg]
        exact h))
      rw [hq,map_pow,hz,one_pow,one_pow]
  rcases BinaryPlaneCubicOrFixedVector.dichotomy (localStabilizer C).range with hc | hf
  · obtain ⟨a,ha,han⟩ := hc
    obtain ⟨q,hq⟩ := a.property
    have hs : a^2=1 := by
      apply Subtype.ext
      simpa only [Subgroup.coe_pow,Subgroup.coe_one,hq] using hsquare q
    have he : a^3=a := by rw [pow_succ,hs,one_mul]
    exact False.elim (han (he.symm.trans ha))
  · obtain ⟨v,hv,hfixed⟩ := hf
    apply BinaryPlaneInvariantLineFrame.exists_frame C heven v hv
    intro q hq
    exact hfixed ⟨localStabilizer C ⟨q,hq⟩,⟨⟨q,hq⟩,rfl⟩⟩

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulUntwistedLineFrame
