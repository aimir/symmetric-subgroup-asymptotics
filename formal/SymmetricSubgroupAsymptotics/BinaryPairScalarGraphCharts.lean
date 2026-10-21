import SymmetricSubgroupAsymptotics.BinaryPairLayerGraphCoefficients
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerDimension
import SymmetricSubgroupAsymptotics.BinaryRegular46GraphHeadRigidity
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14GraphHeadRigidity
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads

/-! The two and eight scalar graph charts are exactly the original module
states with the retained layers. Only displayed basis equations are finite;
all original functions are covered by the exact layer-dimension theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def binaryEightParity : (Fin 8 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  binaryRowFunctional (binaryVectorOfMask 8 255)

theorem regular45_eq_parity_kernel :
    (BinaryRegularEightNaturalRegistry.charts 45).2.space = binaryEightParity.ker := by
  rw [← BinaryRegularEightNaturalRegistry.states_space,
    BinaryRegularEightNaturalRegistry.kernel45_space]
  ext v
  simp only [BinaryRegularEightSquareCarry.K45,
    BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf,
    LinearMap.mem_ker, binaryEightParity]
  constructor
  · intro h
    exact h 0
  · intro h i
    fin_cases i
    exact h

namespace BinaryRegular46GraphHeadRigidity

def sumChart : BinaryCoordinateSpace 8 1 := (BinaryRegularEightNaturalRegistry.charts 23).2

def coefficientForm (p : Fin 2) : Fin 1 → ZMod 2 := binaryVectorOfMask 1 p.val

theorem coefficientForm_surjective : Function.Surjective coefficientForm := by
  unfold Function.Surjective coefficientForm
  decide +kernel

private theorem graph_basis : ∀ p j,
    (BinaryPairFrame.pairLayerFlatten.symm ((stateChart p).inclusion (Pi.single j 1))).2 ∈ sumChart.space ∧
    binaryEightParity
      (BinaryPairFrame.pairLayerFlatten.symm ((stateChart p).inclusion (Pi.single j 1))).1 =
      ∑ i, sumChart.coordinates
        (BinaryPairFrame.pairLayerFlatten.symm ((stateChart p).inclusion (Pi.single j 1))).2 i *
          coefficientForm p i := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

end BinaryRegular46GraphHeadRigidity

namespace BinaryHeisenberg14GraphHeadRigidity

def sumChart : BinaryCoordinateSpace 8 3 := (BinaryHeisenbergEightNaturalHeads.charts 14).2

def coefficientForm (p : Fin 8) : Fin 3 → ZMod 2 := binaryVectorOfMask 3 p.val

theorem coefficientForm_surjective : Function.Surjective coefficientForm := by
  unfold Function.Surjective coefficientForm
  decide +kernel

private theorem graph_basis : ∀ p j,
    (BinaryPairFrame.pairLayerFlatten.symm ((stateChart p).inclusion (Pi.single j 1))).2 ∈ sumChart.space ∧
    binaryEightParity
      (BinaryPairFrame.pairLayerFlatten.symm ((stateChart p).inclusion (Pi.single j 1))).1 =
      ∑ i, sumChart.coordinates
        (BinaryPairFrame.pairLayerFlatten.symm ((stateChart p).inclusion (Pi.single j 1))).2 i *
          coefficientForm p i := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

end BinaryHeisenberg14GraphHeadRigidity

namespace BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))

@[simp] theorem pairSum_originalCoordinateEquiv_symm (v : Fin (w+w) → ZMod 2) :
    F.pairSum (F.originalCoordinateEquiv.symm v) = (pairLayerFlatten.symm v).2 := by
  exact congrArg Prod.snd (F.pairLayerCoordinateEquiv.apply_symm_apply (pairLayerFlatten.symm v))

@[simp] theorem pairZero_originalCoordinateEquiv_symm (v : Fin (w+w) → ZMod 2) :
    F.pairZeroRestriction (F.originalCoordinateEquiv.symm v) = (pairLayerFlatten.symm v).1 := by
  exact congrArg Prod.fst (F.pairLayerCoordinateEquiv.apply_symm_apply (pairLayerFlatten.symm v))

end BinaryPairFrame

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8))

theorem regular_parity_layers_exists_original_graph_chart
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hS : (F.pairSumModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (hL : (F.pairConstantModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 45).2.space) :
    ∃ p : Fin 2, (F.originalCoordinateSubrepresentation W).toSubmodule =
      (BinaryRegular46GraphHeadRigidity.stateChart p).space := by
  have hL' := hL.trans regular45_eq_parity_kernel
  obtain ⟨c,hgraph⟩ := F.exists_pairModule_graph_coefficients W
    BinaryRegular46GraphHeadRigidity.sumChart hS binaryEightParity hL'
  obtain ⟨p,hp⟩ := BinaryRegular46GraphHeadRigidity.coefficientForm_surjective c
  refine ⟨p,F.originalCoordinateSubrepresentation_eq_chart W _ ?_ ?_⟩
  · rw [hS,hL]
    have hs := (BinaryRegularEightNaturalRegistry.charts 23).2.finrank
    have hl := (BinaryRegularEightNaturalRegistry.charts 45).2.finrank
    change Module.finrank (ZMod 2) (BinaryRegularEightNaturalRegistry.charts 23).2.space +
      Module.finrank (ZMod 2) (BinaryRegularEightNaturalRegistry.charts 45).2.space = 8
    rw [hs,hl]
    decide
  · intro j
    rw [hgraph]
    simp only [pairSum_originalCoordinateEquiv_symm,pairZero_originalCoordinateEquiv_symm,← hp]
    exact BinaryRegular46GraphHeadRigidity.graph_basis p j

theorem heisenberg_parity_layers_exists_original_graph_chart
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hS : (F.pairSumModuleLayer W).toSubmodule = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space)
    (hL : (F.pairConstantModuleLayer W).toSubmodule = (BinaryHeisenbergEightNaturalHeads.charts 12).2.space) :
    ∃ p : Fin 8, (F.originalCoordinateSubrepresentation W).toSubmodule =
      (BinaryHeisenberg14GraphHeadRigidity.stateChart p).space := by
  have hL' : (F.pairConstantModuleLayer W).toSubmodule = binaryEightParity.ker :=
    hL.trans regular45_eq_parity_kernel
  obtain ⟨c,hgraph⟩ := F.exists_pairModule_graph_coefficients W
    BinaryHeisenberg14GraphHeadRigidity.sumChart hS binaryEightParity hL'
  obtain ⟨p,hp⟩ := BinaryHeisenberg14GraphHeadRigidity.coefficientForm_surjective c
  refine ⟨p,F.originalCoordinateSubrepresentation_eq_chart W _ ?_ ?_⟩
  · rw [hS,hL]
    have hs := (BinaryHeisenbergEightNaturalHeads.charts 14).2.finrank
    have hl := (BinaryHeisenbergEightNaturalHeads.charts 12).2.finrank
    change Module.finrank (ZMod 2) (BinaryHeisenbergEightNaturalHeads.charts 14).2.space +
      Module.finrank (ZMod 2) (BinaryHeisenbergEightNaturalHeads.charts 12).2.space = 10
    rw [hs,hl]
    decide
  · intro j
    rw [hgraph]
    simp only [pairSum_originalCoordinateEquiv_symm,pairZero_originalCoordinateEquiv_symm,← hp]
    exact BinaryHeisenberg14GraphHeadRigidity.graph_basis p j

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
