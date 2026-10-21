import SymmetricSubgroupAsymptotics.BinaryPairDegreeEightAxisModels
import SymmetricSubgroupAsymptotics.BinaryPairDegreeEightSaturatedExponent

/-! The fifteen natural-kernel states and their full intrinsic radicals
are the SAME original correlated pair kernel, for arbitrary affine lifts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryHeisenbergEightNaturalHeads
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem heisenberg_all_kernel_models (hH : F.top.range = H) :
    ∃ i : Fin 15, F.kernelSpace = (charts i).2.space ∧
      F.ambientAxis (primeRelativeRadical 2 F.top.ker) = (radicalCharts i).2.space := by
  let W := F.literalTopAxis H hH F.top.ker
  obtain ⟨i,hi⟩ := complete W
  have hs : W.toSubmodule = F.kernelSpace :=
    (F.literalTopAxis_space H hH F.top.ker).trans F.ambientAxis_kernel
  have hr : F.ambientAxis (primeRelativeRadical 2 F.top.ker) =
      (Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype :=
    (F.ambientAxis_radical_eq_coinvariants_radical F.top.ker le_rfl).trans
      (F.literalTopAxis_radical H hH F.top.ker).symm
  refine ⟨i,?_,?_⟩
  · exact hs.symm.trans ((congrArg Subrepresentation.toSubmodule hi.symm).trans (states_space i))
  · rw [← hi] at hr
    exact hr.trans (coinvariantsKer_map_eq_radical i)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
