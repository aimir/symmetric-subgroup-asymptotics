import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointZeroFrames
import SymmetricSubgroupAsymptotics.BinaryPairElementaryKernelSplit
import SymmetricSubgroupAsymptotics.BinaryDegreeEightElementaryActionCoverage
import SymmetricSubgroupAsymptotics.BinaryPairFrameConjugateTop

/-! An original exponent-two transitive degree-sixteen source has a
literal constant-kernel regular-eight zero frame on the SAME group/points.
Only checked degree-eight action coverage is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics

private theorem regularEight_constantChart :
    (BinaryRegularEightNaturalRegistry.charts 23).2.space =
      Submodule.span (ZMod 2) {(1 : Fin 8 → ZMod 2)} := by
  rw [(BinaryRegularEightNaturalRegistry.charts 23).2.space_eq_span_basis]
  congr 1
  ext v
  constructor
  · rintro ⟨j,rfl⟩
    fin_cases j
    change (BinaryRegularEightNaturalRegistry.charts 23).2.inclusion
      (Pi.single (⟨0, by decide⟩ : Fin (BinaryRegularEightNaturalRegistry.charts 23).fst) 1) = 1
    decide +kernel
  · intro hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    refine ⟨⟨0, by decide⟩,?_⟩
    decide +kernel

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]

include F

theorem exists_original_elementary_zero_frame
    (hU : IsPGroup 2 U) (hpow : ∀ u : U, u^2=1) :
    ∃ E : BinaryPairFrame U (Fin 8), U = E.splitAffineAction ∧
      E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) ∧
      E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space := by
  letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
  have htopPow (t : F.top.range) : t^2=1 := by
    obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
    rw [← map_pow,hpow,map_one]
  have hel : BinarySquareActionStructure.SquaresActTrivially
      (G := F.top.range) (X := Fin 8) := by
    intro t i
    rw [htopPow]
    rfl
  obtain ⟨g,hg⟩ := BinaryDegreeEightElementaryActionCoverage.elementary_action_conjugate_regular
    F.top.range (F.top_isPGroup hU)
      (fun i j => MulAction.exists_smul_eq F.top.range i j) hel
  let E := F.reindex g
  have hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) :=
    (F.reindex_top_range_conjugation g).trans hg
  have hlift (i : Fin 3) : ∃ u : U, E.top u = BinaryMenuCayley8T3.generators i := by
    have hm : BinaryMenuCayley8T3.generators i ∈ E.top.range := by
      rw [hH]
      exact Subgroup.subset_closure ⟨i,rfl⟩
    exact hm
  choose u hu using hlift
  have hgen : Subgroup.closure (Set.range fun i => E.top (u i)) = E.top.range := by
    rw [show (fun i => E.top (u i)) = BinaryMenuCayley8T3.generators from funext hu,← hH]
  have hp (i : Fin 3) (j : Fin 8) :
      E.top (u i) j = BinaryRegularEightSquareCarry.generatorImages i j := by
    rw [hu]
    exact (BinaryRegularEightSquareCarry.generatorImages_eq_original i j).symm
  obtain ⟨a,ha⟩ := E.original_elementary_exists_physical_conjugate_zero_offset_model hpow u hp hgen
  have hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space :=
    (E.kernelSpace_eq_constant_of_original_exponent_two hpow).trans regularEight_constantChart.symm
  refine ⟨E.reorient a,E.eq_reoriented_split_of_generated_conjugate u hgen a ha,?_⟩
  simpa only [reorient_top,reorient_kernelSpace] using And.intro hH hK

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
