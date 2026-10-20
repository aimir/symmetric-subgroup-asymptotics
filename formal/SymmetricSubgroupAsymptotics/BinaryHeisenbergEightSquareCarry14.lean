import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarryData

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry.Case14

private def inputMask : Fin 97 → ℕ := ![135,255,135,120,135,39168,65280,39168,39168,26112,0,1966080,1966080,0,0,0,1711276032,1711276032,0,0,30822,21845,53964,21760,53862,85,30924,0,0,0,0,0,0,0,2273771520,3534356504,2865889304,2865889376,3534356576,2273771520,0,1966080,7710,1973790,4921350,11147270,4921350,11147270,2566914048,855639552,1426064896,0,2566914048,855662592,1426087936,0,6291456,6291456,402653184,402653184,101056512,101056512,0,16711680,16711680,16711680,16711680,0,0,0,16711680,16711680,16711800,16711800,135,135,16711680,16719390,7710,39168,16750848,16742430,30750,0,14745600,14745600,14745600,14745600,0,0,0,3782737920,3782737920,2566914048,2566914048,2273771520,2273771520]
private def targetMask : Fin 28 → ℕ := ![135,85,45,85,45,0,135,39168,21760,13056,0,39168,21760,13056,0,0,0,1572864,1572864,393216,393216,0,1610612736,1610612736,0,0,100663296,100663296]
private def combinationMask : Fin 28 → ℕ := ![1,10485760,10485763,10485760,10485763,0,1,32,8388608,8388704,0,32,8388608,8388704,0,0,0,72638187718117475,72638187718117475,72638187718115427,72638187718115427,0,288811004191639651,288811004191639651,0,0,288811004191574115,288811004191574115]
private def input (i : Fin 97) := binaryVectorOfMask 32 (inputMask i)
private def target (i : Fin 28) := binaryVectorOfMask 32 (targetMask i)
private def inputActual (i : Fin 97) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  if h : i.val < 20 then
    squareFunctional ⟨i.val / 5, by omega⟩ (binaryVectorOfMask 8 (annihilatorK14 ⟨i.val % 5, by omega⟩))
  else
    relatorFunctional ⟨(i.val - 20) / 7, by omega⟩ (binaryVectorOfMask 8 (annihilatorR14 ⟨(i.val - 20) % 7, by omega⟩))
private def targetActual (i : Fin 28) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  squareFunctional ⟨i.val / 7, by omega⟩ (binaryVectorOfMask 8 (annihilatorR14 ⟨i.val % 7, by omega⟩))
private theorem input_basis : ∀ i j,
  binaryRowFunctional (input i) (Pi.single j 1) = inputActual i (Pi.single j 1) := by decide +kernel
private theorem target_basis : ∀ i j,
  binaryRowFunctional (target i) (Pi.single j 1) = targetActual i (Pi.single j 1) := by decide +kernel
private def certificate : BinaryLinearConstraintCertificate input target where
  support j := Finset.univ.filter fun i => (combinationMask j).testBit i.val
  target_eq := by decide +kernel
theorem square_carry (x : Offsets) (hsquare : ∀ i, squareMap i x ∈ K14)
    (hrelator : ∀ r, relatorMap r x ∈ R14) : ∀ i, squareMap i x ∈ R14 := by
  have hinput (i : Fin 97) : dotProduct (input i) x = 0 := by
    change binaryRowFunctional (input i) x = 0
    rw [binaryLinearFunctional_ext_basis (input_basis i)]
    unfold inputActual
    split_ifs with h
    · have hs := hsquare (⟨i.val / 5, by omega⟩ : Fin 4)
      simp only [K14, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hs
      exact hs ⟨i.val % 5, by omega⟩
    · have hr := hrelator (⟨(i.val - 20) / 7, by omega⟩ : Fin 11)
      simp only [R14, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hr
      exact hr ⟨(i.val - 20) % 7, by omega⟩
  intro i
  simp only [R14, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro chi
  have ht := certificate.target_dotProduct_eq_zero x hinput (⟨7 * i.val + chi.val, by omega⟩ : Fin 28)
  change binaryRowFunctional (target _) x = 0 at ht
  rw [binaryLinearFunctional_ext_basis (target_basis _)] at ht
  have hd : (7 * i.val + chi.val) / 7 = i.val := by omega
  have hm : (7 * i.val + chi.val) % 7 = chi.val := by omega
  simpa only [targetActual, hd, hm] using ht

end SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry.Case14
