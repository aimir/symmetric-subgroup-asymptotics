import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantRadicalBinding
import SymmetricSubgroupAsymptotics.BinaryRegularSixCanonicalGenerators

/-! Literal state and generator bindings between the original affine-row
packet and the outer carry packet. Only chart columns and individual
permutation points are checked; no action or submodule census is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantStateBinding
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BinaryRegular46FullConstantOuterCarries
abbrev S := BinarySplitRegular46FullConstantStabilizer.state
private def constraints : V →ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun v i := binaryRowFunctional (binaryVectorOfMask 16 (stateAnnihilator i)) v
  map_add' v z := by funext i;exact map_add (binaryRowFunctional _) v z
  map_smul' c v := by funext i;exact map_smul (binaryRowFunctional _) c v
private def testSection : (Fin 4 → ZMod 2) →ₗ[ZMod 2] V :=
  (binaryRectangularMatrixOfColumnMasks 16 4
    (![256,512,1024,2048] : Fin 4 → ℕ)).mulVecLin
private def defect : V →ₗ[ZMod 2] V := S.inclusion.comp S.coordinates - LinearMap.id
private theorem chart_columns_zero : ∀ j : Fin 12,
    constraints (S.inclusion (Pi.single j 1)) = 0 := by decide +kernel
private theorem defect_columns : ∀ j : Fin 16,
    S.inclusion (S.coordinates (Pi.single j 1)) - Pi.single j 1 =
      (defect.comp testSection) (constraints (Pi.single j 1)) := by decide +kernel

theorem state_eq_wideState : S.space = wideState := by
  rw [S.space_eq_ker_of_basis_factor constraints (defect.comp testSection)
    chart_columns_zero defect_columns]
  ext v
  constructor
  · intro hv
    apply (Submodule.mem_iInf _).mpr
    intro i
    have hz : constraints v = 0 := hv
    exact congrFun hz i
  · intro hv
    change constraints v = 0
    funext i
    exact (Submodule.mem_iInf _).mp hv i

private theorem generator_points : ∀ i : Fin 6, ∀ j : Fin 16,
    BinaryRegularSixCanonicalGenerators.generators i j = generatorImages i j := by decide +kernel

theorem generators_eq : BinaryRegularSixCanonicalGenerators.generators = generators := by
  funext i
  exact Equiv.ext (generator_points i)

theorem layerChange_eq : layerChange = binaryEightCanonicalLayerChange := rfl

end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantStateBinding
