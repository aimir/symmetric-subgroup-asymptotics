import SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroIntrinsicRadical
import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaceKernelEquality

/-! The original graph-state chart and intrinsic radical chart agree
with the literal square-carry annihilator denominators. Identities are
proved on11/5 chart columns and16 defect columns, not all binary vectors. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroCarryCoordinates
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BinaryElementary16PhiZeroOuterCarries
abbrev S := BinaryElementary16GraphHeadRigidity.stateChart 0
abbrev R := BinaryElementaryPhiZeroIntrinsicRadical.radical

private def constraints {q : ℕ} (masks : Fin q → ℕ) :
    V →ₗ[ZMod 2] (Fin q → ZMod 2) where
  toFun v i := binaryRowFunctional (binaryVectorOfMask 16 (masks i)) v
  map_add' v z := by funext i;exact map_add (binaryRowFunctional _) v z
  map_smul' c v := by funext i;exact map_smul (binaryRowFunctional _) c v
private theorem constraints_ker {q : ℕ} (masks : Fin q → ℕ) :
    (constraints masks).ker = annihilatorSpace masks := by
  ext v
  constructor
  · intro hv
    apply (Submodule.mem_iInf _).mpr
    intro i
    have hz : constraints masks v = 0 := hv
    exact congrFun hz i
  · intro hv
    change constraints masks v = 0
    funext i
    exact (Submodule.mem_iInf _).mp hv i
private def stateSection : (Fin 5 → ZMod 2) →ₗ[ZMod 2] V :=
  (binaryRectangularMatrixOfColumnMasks 16 5
    (![1,256,512,1024,2048] : Fin 5 → ℕ)).mulVecLin
private def radicalSection : (Fin 11 → ZMod 2) →ₗ[ZMod 2] V :=
  (binaryRectangularMatrixOfColumnMasks 16 11
    (![1,2,4,8,256,512,1024,2048,4096,8192,16384] : Fin 11 → ℕ)).mulVecLin
private def stateDefect : V →ₗ[ZMod 2] V := S.inclusion.comp S.coordinates - LinearMap.id
private def radicalDefect : V →ₗ[ZMod 2] V := R.inclusion.comp R.coordinates - LinearMap.id
private theorem state_columns_zero : ∀ j : Fin 11,
    constraints stateAnnihilator (S.inclusion (Pi.single j 1)) = 0 := by decide +kernel
private theorem state_defect_columns : ∀ j : Fin 16,
    S.inclusion (S.coordinates (Pi.single j 1)) - Pi.single j 1 =
      (stateDefect.comp stateSection) (constraints stateAnnihilator (Pi.single j 1)) := by decide +kernel
private theorem radical_columns_zero : ∀ j : Fin 5,
    constraints radicalAnnihilator (R.inclusion (Pi.single j 1)) = 0 := by decide +kernel
private theorem radical_defect_columns : ∀ j : Fin 16,
    R.inclusion (R.coordinates (Pi.single j 1)) - Pi.single j 1 =
      (radicalDefect.comp radicalSection) (constraints radicalAnnihilator (Pi.single j 1)) := by decide +kernel

theorem state_eq_wideState : S.space = wideState :=
  (S.space_eq_ker_of_basis_factor (constraints stateAnnihilator) (stateDefect.comp stateSection)
    state_columns_zero state_defect_columns).trans (constraints_ker stateAnnihilator)

theorem radical_eq_lowerRadical : R.space = lowerRadical :=
  (R.space_eq_ker_of_basis_factor (constraints radicalAnnihilator) (radicalDefect.comp radicalSection)
    radical_columns_zero radical_defect_columns).trans (constraints_ker radicalAnnihilator)

theorem layerChange_eq : layerChange = binaryEightCanonicalLayerChange := rfl

end SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroCarryCoordinates
