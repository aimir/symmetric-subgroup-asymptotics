import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Dimensions of the two actual layers determine the dimension of the
same correlated original point submodule. A reversible chart is identified
by basis containment and this exact dimension, without assignment census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem pairModuleLayers_finrank
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toSubmodule =
      Module.finrank (ZMod 2) (F.pairSumModuleLayer W).toSubmodule +
        Module.finrank (ZMod 2) (F.pairConstantModuleLayer W).toSubmodule := by
  let q := (F.pairSumLayerProjection W).toLinearMap
  let i := (F.pairConstantLayerInclusion W).toLinearMap
  have hi : Function.Injective i := by
    intro v z he
    apply Subtype.ext
    apply F.pairConstant_injective
    exact congrArg Subtype.val he
  have hq : q.range = ⊤ := LinearMap.range_eq_top.mpr (F.pairSumLayerProjection_surjective W)
  have he : i.range = q.ker := F.pairModuleLayers_exact W
  have hdim := q.finrank_range_add_finrank_ker
  have ht : Module.finrank (ZMod 2)
      (⊤ : Submodule (ZMod 2) (F.pairSumModuleLayer W).toSubmodule) =
      Module.finrank (ZMod 2) (F.pairSumModuleLayer W).toSubmodule :=
    (Submodule.topEquiv :
      (⊤ : Submodule (ZMod 2) (F.pairSumModuleLayer W).toSubmodule) ≃ₗ[ZMod 2]
        (F.pairSumModuleLayer W).toSubmodule).finrank_eq
  rw [hq, ht, ← he, LinearMap.finrank_range_of_inj hi] at hdim
  exact hdim.symm

/-- Literal basis containment suffices once both original layer dimensions
have been retained. -/
theorem originalCoordinateSubrepresentation_eq_chart {d : ℕ}
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (C : BinaryCoordinateSpace (w+w) d)
    (hdim : Module.finrank (ZMod 2) (F.pairSumModuleLayer W).toSubmodule +
      Module.finrank (ZMod 2) (F.pairConstantModuleLayer W).toSubmodule = d)
    (hbasis : ∀ j, F.originalCoordinateEquiv.symm (C.inclusion (Pi.single j 1)) ∈ W.toSubmodule) :
    (F.originalCoordinateSubrepresentation W).toSubmodule = C.space := by
  have hle : C.space ≤ (F.originalCoordinateSubrepresentation W).toSubmodule := by
    apply C.le_of_basis_mem
    intro j
    exact (F.mem_originalCoordinateSubrepresentation_iff W _).mpr (hbasis j)
  have hdimW : Module.finrank (ZMod 2) W.toSubmodule = d :=
    (F.pairModuleLayers_finrank W).trans hdim
  have hdimC : Module.finrank (ZMod 2) C.space =
      Module.finrank (ZMod 2) (F.originalCoordinateSubrepresentation W).toSubmodule := by
    rw [C.finrank]
    exact hdimW.symm.trans (F.originalCoordinateEquiv.submoduleMap W.toSubmodule).finrank_eq
  exact (Submodule.eq_of_le_of_finrank_eq hle hdimC).symm

end SymmetricSubgroupAsymptotics.BinaryPairFrame
