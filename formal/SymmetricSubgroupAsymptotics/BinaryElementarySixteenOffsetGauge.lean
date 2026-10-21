import SymmetricSubgroupAsymptotics.BinaryLinearSolutionChart
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.BinaryRegularEightSquareCarry

/-! Sparse original-generator offset normalization for the literal regular
elementary source. Every24-bit assignment with exact zero square and
commutator offsets has an actual physical orientation removing all offsets. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryElementarySixteenOffsetGauge
open BinaryRegularEightSquareCarry

abbrev Gauge := Fin 8 → ZMod 2
private def inputMasks : Fin 48 → ℕ := ![129,6,6,24,24,96,96,129,1280,33280,1280,10240,20480,10240,20480,33280,1114112,2228224,4456448,8912896,1114112,2228224,4456448,8912896,33029,1666,1541,6184,6224,24616,24656,33154,8454161,393250,393284,1573000,1572881,6291490,6291524,8454280,332032,8528384,345088,2656256,5247232,2630144,5260288,8554496]
private def basisMasks : Fin 7 → ℕ := ![8923160,4457734,2238560,1115518,43622,21862,255]
private def coordinateMasks : Fin 24 → ℕ := ![0,0,0,0,0,0,0,64,0,0,0,0,0,0,32,16,0,0,0,0,8,4,2,1]
private def rowCombinationMasks : Fin 24 → ℕ := ![1,1099528736771,1099528736769,4295032841,4295032833,1108118540291,1108118540323,0,1099511959552,512,1099511959808,1112547655690,4096,1112547657738,0,0,65536,131072,262144,524288,0,0,0,0]
private def gaugeMasks : Fin 8 → ℕ := ![1115521,2261510,4457734,8923160,1134616,2238560,4477024,8946305]
private def factorMasks : Fin 7 → ℕ := ![8,4,32,84,34,68,85]
private def inclusion := (binaryRectangularMatrixOfColumnMasks 24 7 basisMasks).mulVecLin
private def coordinates := (binaryRectangularMatrixOfColumnMasks 7 24 coordinateMasks).mulVecLin
private theorem chart_basis : ∀ i : Fin 7,
    coordinates (inclusion (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem chart_left_inverse (v : Fin 7 → ZMod 2) : coordinates (inclusion v) = v := by
  have he : coordinates.comp inclusion = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.comp_apply, hs, map_smul, chart_basis, LinearMap.id_apply]
  exact DFunLike.congr_fun he v
private def solutionChart : BinaryCoordinateSpace 24 7 where
  inclusion := inclusion
  coordinates := coordinates
  left_inverse := chart_left_inverse
private def input (i : Fin 48) : Offsets := binaryVectorOfMask 24 (inputMasks i)
private def rowCertificate : BinaryLinearConstraintCertificate input
    (binaryCoordinateDefectRows solutionChart) where
  support j := Finset.univ.filter fun i => (rowCombinationMasks j).testBit i.val
  target_eq := by decide +kernel
private def gauge : Gauge →ₗ[ZMod 2] Offsets :=
  (binaryRectangularMatrixOfColumnMasks 24 8 gaugeMasks).mulVecLin
private def factor : BinaryCoordinateFactorCertificate solutionChart gauge where
  lift := (binaryRectangularMatrixOfColumnMasks 8 7 factorMasks).mulVecLin
  basis_eq := by decide +kernel

private def inputActual (k : Fin 48) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  if h : k.val < 24 then
    squareFunctional ⟨k.val / 8, by omega⟩ (Pi.single ⟨k.val % 8, by omega⟩ 1)
  else
    commutatorFunctional ⟨(k.val - 24) / 8, by omega⟩
      (Pi.single ⟨(k.val - 24) % 8, by omega⟩ 1)
private theorem input_basis : ∀ i j,
    binaryRowFunctional (input i) (Pi.single j 1) = inputActual i (Pi.single j 1) := by
  decide +kernel
private def orientation : Gauge →ₗ[ZMod 2] V := LinearMap.id
private def orientationPullback (i : Fin 3) : V →ₗ[ZMod 2] V where
  toFun a j := a (generatorImages i j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def sourceCorrection (i : Fin 3) : Gauge →ₗ[ZMod 2] V :=
  (offsetProjection i).comp gauge + (orientationPullback i).comp orientation - orientation
private theorem correction_basis : ∀ i j k,
    sourceCorrection i (Pi.single k 1) j = 0 := by decide +kernel
private theorem correction_zero (i : Fin 3) (y : Gauge) : sourceCorrection i y = 0 := by
  funext j
  have he : (LinearMap.proj j).comp (sourceCorrection i) = 0 :=
    binaryLinearFunctional_ext_basis (fun k => correction_basis i j k)
  exact congrArg (fun f : (Gauge →ₗ[ZMod 2] ZMod 2) => f y) he

/-- Exact original square/commutator offsets vanish after one physical
pair-orientation change. No kernel or complement premise is used. -/
theorem exists_source_orientation (x : Offsets)
    (hsquare : ∀ i, squareDisplacement i x = 0)
    (hcomm : ∀ p, commutatorDisplacement (pairs p).1 (pairs p).2 x = 0) :
    ∃ a : V, ∀ i, offsetProjection i x + (fun j => a (generatorImages i j)) - a = 0 := by
  have hi (i : Fin 48) : dotProduct (input i) x = 0 := by
    change binaryRowFunctional (input i) x = 0
    rw [binaryLinearFunctional_ext_basis (input_basis i)]
    unfold inputActual
    split_ifs with h
    · change binaryRowFunctional (Pi.single (⟨i.val % 8, by omega⟩ : Fin 8) 1)
        (squareDisplacement ⟨i.val / 8, by omega⟩ x) = 0
      rw [hsquare, map_zero]
    · change binaryRowFunctional (Pi.single (⟨(i.val - 24) % 8, by omega⟩ : Fin 8) 1)
        (commutatorDisplacement (pairs ⟨(i.val - 24) / 8, by omega⟩).1
          (pairs ⟨(i.val - 24) / 8, by omega⟩).2 x) = 0
      rw [hcomm, map_zero]
  have hx := binaryCoordinate_mem_of_constraints solutionChart input rowCertificate x hi
  obtain ⟨y, hy⟩ := factor.exists_actual_gauge_coordinates x hx
  refine ⟨orientation y, ?_⟩
  intro i
  rw [← hy]
  exact correction_zero i y

end SymmetricSubgroupAsymptotics.BinaryElementarySixteenOffsetGauge
