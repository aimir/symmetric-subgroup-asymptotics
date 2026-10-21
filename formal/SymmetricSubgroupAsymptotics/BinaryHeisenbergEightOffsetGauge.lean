import SymmetricSubgroupAsymptotics.BinaryLinearSolutionChart
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarryData

/-! Sparse original-generator offset normalization for the literal regular
K14 kernel. Every32-bit assignment satisfying the same square and derived
carry constraints has an actual physical orientation gauge modulo K14. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergEightOffsetGauge
open BinaryHeisenbergEightSquareCarry

abbrev Gauge := Fin 20 → ZMod 2
private def inputMasks : Fin 97 → ℕ := ![135,255,135,120,135,39168,65280,39168,39168,26112,0,1966080,1966080,0,0,0,1711276032,1711276032,0,0,30822,21845,53964,21760,53862,85,30924,0,0,0,0,0,0,0,2273771520,3534356504,2865889304,2865889376,3534356576,2273771520,0,1966080,7710,1973790,4921350,11147270,4921350,11147270,2566914048,855639552,1426064896,0,2566914048,855662592,1426087936,0,6291456,6291456,402653184,402653184,101056512,101056512,0,16711680,16711680,16711680,16711680,0,0,0,16711680,16711680,16711800,16711800,135,135,16711680,16719390,7710,39168,16750848,16742430,30750,0,14745600,14745600,14745600,14745600,0,0,0,3782737920,3782737920,2566914048,2566914048,2273771520,2273771520]
private def basisMasks : Fin 15 → ℕ := ![2164269608,1610621480,402661928,100672040,8454189,6291501,1572909,393261,34560,26112,4357,3845,135,102,30]
private def coordinateMasks : Fin 32 → ℕ := ![0,0,0,0,16384,0,8192,4096,0,0,0,2048,1024,0,512,256,0,0,128,0,64,0,32,16,0,0,8,0,4,0,2,1]
private def rowCombinationMasks : Fin 32 → ℕ := ![72092778410018817,10485761,72092778420504577,360868632589238371,0,360868632589238368,0,0,32,288846222930741280,8388640,0,0,288846222922352736,0,0,72110370596061184,72638187718115427,0,72638187718117475,0,72057594037927936,0,0,288283272968996864,288811004191574115,0,288230376151711744,0,288811004191639651,0,0]
private def gaugeMasks : Fin 20 → ℕ := ![135,102,30,34560,26112,7680,8847360,6684672,1966080,2264924160,1711276032,503316480,4357,101065346,101073925,1607720,1577296,1610621480,1610630224,34946]
private def factorMasks : Fin 15 → ℕ := ![45865,46377,47401,45353,37224,37288,36904,37160,8,16,4096,4128,1,2,4]
private def inclusion := (binaryRectangularMatrixOfColumnMasks 32 15 basisMasks).mulVecLin
private def coordinates := (binaryRectangularMatrixOfColumnMasks 15 32 coordinateMasks).mulVecLin
private theorem chart_basis : ∀ i : Fin 15,
    coordinates (inclusion (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem chart_left_inverse (v : Fin 15 → ZMod 2) : coordinates (inclusion v) = v := by
  have he : coordinates.comp inclusion = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.comp_apply, hs, map_smul, chart_basis, LinearMap.id_apply]
  exact DFunLike.congr_fun he v
private def solutionChart : BinaryCoordinateSpace 32 15 where
  inclusion := inclusion
  coordinates := coordinates
  left_inverse := chart_left_inverse
private def input (i : Fin 97) : Offsets := binaryVectorOfMask 32 (inputMasks i)
private def rowCertificate : BinaryLinearConstraintCertificate input
    (binaryCoordinateDefectRows solutionChart) where
  support j := Finset.univ.filter fun i => (rowCombinationMasks j).testBit i.val
  target_eq := by decide +kernel
private def gauge : Gauge →ₗ[ZMod 2] Offsets :=
  (binaryRectangularMatrixOfColumnMasks 32 20 gaugeMasks).mulVecLin
private def factor : BinaryCoordinateFactorCertificate solutionChart gauge where
  lift := (binaryRectangularMatrixOfColumnMasks 20 15 factorMasks).mulVecLin
  basis_eq := by decide +kernel

private def inputActual (k : Fin 97) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  if h : k.val < 20 then
    squareFunctional ⟨k.val / 5, by omega⟩
      (binaryVectorOfMask 8 (annihilatorK14 ⟨k.val % 5, by omega⟩))
  else
    relatorFunctional ⟨(k.val - 20) / 7, by omega⟩
      (binaryVectorOfMask 8 (annihilatorR14 ⟨(k.val - 20) % 7, by omega⟩))
private theorem input_basis : ∀ i j,
    binaryRowFunctional (input i) (Pi.single j 1) = inputActual i (Pi.single j 1) := by
  decide +kernel
private def orientation : Gauge →ₗ[ZMod 2] V where
  toFun y j := y ⟨12 + j.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def orientationPullback (i : Fin 4) : V →ₗ[ZMod 2] V where
  toFun a j := a (originalSelected i j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def gaugeProjection (i : Fin 4) : Offsets →ₗ[ZMod 2] V :=
  (LinearMap.proj i).comp unflatten
private def sourceCorrection (i : Fin 4) : Gauge →ₗ[ZMod 2] V :=
  (gaugeProjection i).comp gauge + (orientationPullback i).comp orientation - orientation
private theorem correction_basis : ∀ i chi j,
    binaryRowFunctional (binaryVectorOfMask 8 (annihilatorK14 chi))
      (sourceCorrection i (Pi.single j 1)) = 0 := by decide +kernel
private theorem correction_mem (i : Fin 4) (y : Gauge) : sourceCorrection i y ∈ K14 := by
  simp only [K14, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro chi
  have he : (binaryRowFunctional (binaryVectorOfMask 8 (annihilatorK14 chi))).comp
      (sourceCorrection i) = 0 :=
    binaryLinearFunctional_ext_basis (fun j => correction_basis i chi j)
  exact congrArg (fun f : (Gauge →ₗ[ZMod 2] ZMod 2) => f y) he

/-- The actual source offsets can all be removed modulo the SAME kernel
by one physical pair-orientation vector. -/
theorem exists_source_orientation (x : Offsets)
    (hsquare : ∀ i, squareMap i x ∈ K14)
    (hrelator : ∀ r, relatorMap r x ∈ R14) :
    ∃ a : V, ∀ i, unflatten x i + (fun j => a (originalSelected i j)) - a ∈ K14 := by
  have hi (i : Fin 97) : dotProduct (input i) x = 0 := by
    change binaryRowFunctional (input i) x = 0
    rw [binaryLinearFunctional_ext_basis (input_basis i)]
    unfold inputActual
    split_ifs with h
    · have hs := hsquare (⟨i.val / 5, by omega⟩ : Fin 4)
      simp only [K14, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hs
      exact hs ⟨i.val % 5, by omega⟩
    · have hc := hrelator (⟨(i.val - 20) / 7, by omega⟩ : Fin 11)
      simp only [R14, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hc
      exact hc ⟨(i.val - 20) % 7, by omega⟩
  have hx := binaryCoordinate_mem_of_constraints solutionChart input rowCertificate x hi
  obtain ⟨y, hy⟩ := factor.exists_actual_gauge_coordinates x hx
  refine ⟨orientation y, ?_⟩
  intro i
  rw [← hy]
  exact correction_mem i y

end SymmetricSubgroupAsymptotics.BinaryHeisenbergEightOffsetGauge
