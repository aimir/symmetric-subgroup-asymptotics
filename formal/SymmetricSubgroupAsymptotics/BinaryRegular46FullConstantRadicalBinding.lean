import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesDefinitions
import SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantStabilizerData
import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaceKernelEquality

/-! The literal radical chart of the checked original-row packet equals
the literal annihilator denominator of the square-carry packet. Equality
is checked on eight chart columns and sixteen defect columns, not on all
sixteen-bit vectors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantRadicalBinding
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BinaryRegular46FullConstantOuterCarries
abbrev R := BinarySplitRegular46FullConstantStabilizer.radical

private def constraints : V →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun v i := binaryRowFunctional (binaryVectorOfMask 16 (radicalAnnihilator i)) v
  map_add' v z := by
    funext i
    exact map_add (binaryRowFunctional _) v z
  map_smul' c v := by
    funext i
    exact map_smul (binaryRowFunctional _) c v

private def testSection : (Fin 8 → ZMod 2) →ₗ[ZMod 2] V :=
  (binaryRectangularMatrixOfColumnMasks 16 8
    (![1,256,512,1024,2048,4096,8192,16384] : Fin 8 → ℕ)).mulVecLin

private def defect : V →ₗ[ZMod 2] V := R.inclusion.comp R.coordinates - LinearMap.id

private theorem chart_columns_zero : ∀ j : Fin 8,
    constraints (R.inclusion (Pi.single j 1)) = 0 := by decide +kernel

private theorem defect_columns : ∀ j : Fin 16,
    R.inclusion (R.coordinates (Pi.single j 1)) - Pi.single j 1 =
      (defect.comp testSection) (constraints (Pi.single j 1)) := by decide +kernel

theorem radical_eq_lowerRadical : R.space = lowerRadical := by
  have he := R.space_eq_ker_of_basis_factor constraints (defect.comp testSection)
    chart_columns_zero defect_columns
  rw [he]
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

end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantRadicalBinding
