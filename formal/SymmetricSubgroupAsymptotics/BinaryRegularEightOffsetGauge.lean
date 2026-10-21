import SymmetricSubgroupAsymptotics.BinaryLinearSolutionChart
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.BinaryRegularEightSquareCarry

/-! Sparse original-generator offset normalization for the literal regular
K46 kernel. Every24-bit assignment satisfying the same square and derived
carry constraints has an actual physical orientation gauge modulo K46. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularEightOffsetGauge
open BinaryRegularEightSquareCarry

abbrev Gauge := Fin 20 → ZMod 2
private def inputMasks : Fin 33 → ℕ := ![0,255,255,0,0,65280,0,65280,16711680,16711680,16711680,16711680,135,57685,57645,39253,39213,34560,34695,153,14745685,14745651,10027008,10027161,8847445,8847411,8886528,5592320,2962176,5570560,2988288,21760,8860416]
private def basisMasks : Fin 13 → ℕ := ![8847360,4457734,2229510,1115398,984326,34560,19200,11520,7680,135,75,45,30]
private def coordinateMasks : Fin 24 → ℕ := ![0,0,0,0,4096,2048,1024,512,0,0,0,0,256,128,64,32,0,0,0,16,8,4,2,1]
private def rowCombinationMasks : Fin 24 → ℕ := ![528386,5246976,5771266,4098,0,0,0,0,5251072,671129632,676339712,40960,0,0,0,0,4194304,536871168,541065216,0,0,0,0,0]
private def gaugeMasks : Fin 20 → ℕ := ![135,75,45,30,34560,19200,11520,7680,8847360,4915200,2949120,1966080,1115521,2261510,4457734,8923160,1134616,2238560,4477024,8946305]
private def factorMasks : Fin 13 → ℕ := ![256,6657,7169,4097,6145,16,32,64,128,1,2,4,8]
private def inclusion := (binaryRectangularMatrixOfColumnMasks 24 13 basisMasks).mulVecLin
private def coordinates := (binaryRectangularMatrixOfColumnMasks 13 24 coordinateMasks).mulVecLin
private theorem chart_basis : ∀ i : Fin 13,
    coordinates (inclusion (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem chart_left_inverse (v : Fin 13 → ZMod 2) : coordinates (inclusion v) = v := by
  have he : coordinates.comp inclusion = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.comp_apply, hs, map_smul, chart_basis, LinearMap.id_apply]
  exact DFunLike.congr_fun he v
private def solutionChart : BinaryCoordinateSpace 24 13 where
  inclusion := inclusion
  coordinates := coordinates
  left_inverse := chart_left_inverse
private def input (i : Fin 33) : Offsets := binaryVectorOfMask 24 (inputMasks i)
private def rowCertificate : BinaryLinearConstraintCertificate input
    (binaryCoordinateDefectRows solutionChart) where
  support j := Finset.univ.filter fun i => (rowCombinationMasks j).testBit i.val
  target_eq := by decide +kernel
private def gauge : Gauge →ₗ[ZMod 2] Offsets :=
  (binaryRectangularMatrixOfColumnMasks 24 20 gaugeMasks).mulVecLin
private def factor : BinaryCoordinateFactorCertificate solutionChart gauge where
  lift := (binaryRectangularMatrixOfColumnMasks 20 13 factorMasks).mulVecLin
  basis_eq := by decide +kernel

private def inputActual (k : Fin 33) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  if h : k.val < 12 then
    squareFunctional ⟨k.val / 4, by omega⟩
      (binaryVectorOfMask 8 (annihilatorK46 ⟨k.val % 4, by omega⟩))
  else
    commutatorFunctional ⟨(k.val - 12) / 7, by omega⟩
      (binaryVectorOfMask 8 (annihilatorR46 ⟨(k.val - 12) % 7, by omega⟩))
private theorem input_basis : ∀ i j,
    binaryRowFunctional (input i) (Pi.single j 1) = inputActual i (Pi.single j 1) := by
  decide +kernel
private def orientation : Gauge →ₗ[ZMod 2] V where
  toFun y j := y ⟨12 + j.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def orientationPullback (i : Fin 3) : V →ₗ[ZMod 2] V where
  toFun a j := a (generatorImages i j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def sourceCorrection (i : Fin 3) : Gauge →ₗ[ZMod 2] V :=
  (offsetProjection i).comp gauge + (orientationPullback i).comp orientation - orientation
private theorem correction_basis : ∀ i chi j,
    binaryRowFunctional (binaryVectorOfMask 8 (annihilatorK46 chi))
      (sourceCorrection i (Pi.single j 1)) = 0 := by decide +kernel
private theorem correction_mem (i : Fin 3) (y : Gauge) : sourceCorrection i y ∈ K46 := by
  simp only [K46, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro chi
  have he : (binaryRowFunctional (binaryVectorOfMask 8 (annihilatorK46 chi))).comp
      (sourceCorrection i) = 0 :=
    binaryLinearFunctional_ext_basis (fun j => correction_basis i chi j)
  exact congrArg (fun f : (Gauge →ₗ[ZMod 2] ZMod 2) => f y) he

/-- The actual source offsets can all be removed modulo the SAME kernel
by one physical pair-orientation vector. -/
theorem exists_source_orientation (x : Offsets)
    (hsquare : ∀ i, squareDisplacement i x ∈ K46)
    (hcomm : ∀ p, commutatorDisplacement (pairs p).1 (pairs p).2 x ∈ R46) :
    ∃ a : V, ∀ i, offsetProjection i x + (fun j => a (generatorImages i j)) - a ∈ K46 := by
  have hi (i : Fin 33) : dotProduct (input i) x = 0 := by
    change binaryRowFunctional (input i) x = 0
    rw [binaryLinearFunctional_ext_basis (input_basis i)]
    unfold inputActual
    split_ifs with h
    · have hs := hsquare (⟨i.val / 4, by omega⟩ : Fin 3)
      simp only [K46, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hs
      exact hs ⟨i.val % 4, by omega⟩
    · have hc := hcomm (⟨(i.val - 12) / 7, by omega⟩ : Fin 3)
      simp only [R46, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hc
      exact hc ⟨(i.val - 12) % 7, by omega⟩
  have hx := binaryCoordinate_mem_of_constraints solutionChart input rowCertificate x hi
  obtain ⟨y, hy⟩ := factor.exists_actual_gauge_coordinates x hx
  refine ⟨orientation y, ?_⟩
  intro i
  rw [← hy]
  exact correction_mem i y

end SymmetricSubgroupAsymptotics.BinaryRegularEightOffsetGauge
