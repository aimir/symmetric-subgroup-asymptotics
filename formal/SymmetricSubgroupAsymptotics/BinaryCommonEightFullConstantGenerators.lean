import SymmetricSubgroupAsymptotics.BinaryCommonEightTemplateGenerators
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerGraph
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The fourth critical template has a full constant layer. The common
eight shears belong to its original kernel by the exact preimage theorem;
no scalar graph or outer carry certificate is needed for this width bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem canonical_commonMonomial_pairSum : ∀ b : Fin 16,
    BinaryThreeVariablePairMonomialWidth.Allowed (BinaryElementaryPairMonomialWidth.support b) →
      binaryEightCanonicalPairFrame.pairSum (BinaryCommonEightShearCoordinates.originalMonomial b) = 0 ∨
        binaryEightCanonicalPairFrame.pairSum (BinaryCommonEightShearCoordinates.originalMonomial b) = 1 := by
  decide +kernel

namespace BinaryPairFrame
variable {Y : Type} {V : Subgroup (Equiv.Perm Y)} (E : BinaryPairFrame V (Fin 8))

theorem originalPointMonomial_pairSum (b : Fin 16) :
    E.pairSum (E.originalPointMonomial b) =
      binaryEightCanonicalPairFrame.pairSum (BinaryCommonEightShearCoordinates.originalMonomial b) := by
  have hlabel (p : Fin 8 × ZMod 2) : E.canonicalPointLabels (E.frame p) =
      binaryEightPairPointLabels p := by
    change binaryEightPairPointLabels (E.frame.symm (E.frame p)) = _
    rw [Equiv.symm_apply_apply]
  funext i
  change BinaryCommonEightShearCoordinates.originalMonomial b (E.canonicalPointLabels (E.frame (i, 0))) +
      BinaryCommonEightShearCoordinates.originalMonomial b (E.canonicalPointLabels (E.frame (i, 1))) =
    BinaryCommonEightShearCoordinates.originalMonomial b (binaryEightPairPointLabels (i, 0)) +
      BinaryCommonEightShearCoordinates.originalMonomial b (binaryEightPairPointLabels (i, 1))
  rw [hlabel, hlabel]

theorem originalPointMonomial_mem_of_full_constant_layer
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) V Y))
    (hL : (E.pairConstantModuleLayer W).toSubmodule = ⊤)
    (hS : (1 : Fin 8 → ZMod 2) ∈ (E.pairSumModuleLayer W).toSubmodule)
    (b : Fin 16) (hb : BinaryThreeVariablePairMonomialWidth.Allowed
      (BinaryElementaryPairMonomialWidth.support b)) :
    E.originalPointMonomial b ∈ W.toSubmodule := by
  rw [E.pairModule_eq_pairSum_preimage_of_constant_top W hL]
  change E.pairSum (E.originalPointMonomial b) ∈ (E.pairSumModuleLayer W).toSubmodule
  rw [E.originalPointMonomial_pairSum]
  rcases canonical_commonMonomial_pairSum b hb with hz | ho
  · rw [hz]
    exact (E.pairSumModuleLayer W).toSubmodule.zero_mem
  · rwa [ho]

end BinaryPairFrame

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem uniform_generatedBy_six_of_regular_full_constant_kernel
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace = BinaryRegularEightSquareCarry.K46)
    (hS : (E.pairSumModuleLayer (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule =
      (BinaryRegularEightNaturalRegistry.charts 46).2.space)
    (hL : (E.pairConstantModuleLayer (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule =
      (BinaryRegularEightNaturalRegistry.charts 1).2.space) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) 6 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hLtop : (E.pairConstantModuleLayer W).toSubmodule = ⊤ := by
    rw [hL]
    apply Submodule.eq_top_of_finrank_eq
    rw [(BinaryRegularEightNaturalRegistry.charts 1).2.finrank]
    change 8 = Module.finrank (ZMod 2) (Fin 8 → ZMod 2)
    simp
  have hSone : (1 : Fin 8 → ZMod 2) ∈ (E.pairSumModuleLayer W).toSubmodule := by
    rw [hS]
    simp only [BinaryCoordinateSpace.mem_iff]
    decide +kernel
  apply F.uniform_generatedBy_six_of_original_common_shears E hzero
  · intro j
    rw [hH]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  · rw [hK]
    simp only [BinaryRegularEightSquareCarry.K46,
      BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    decide +kernel
  · intro b hb
    have hm := E.originalPointMonomial_mem_of_full_constant_layer W hLtop hSone b hb
    change E.originalPointMonomial b ∈ F.ambientAxis F.top.ker at hm
    exact F.ambientAxis_le_kernelSpace F.top.ker hm

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
