import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarryData

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry.Case13

private def inputMask : Fin 67 → ℕ := ![0,255,255,65280,0,65280,0,0,0,0,0,0,30822,65535,30822,34662,30873,0,0,0,0,0,2273771520,120,2021130360,2021130240,2273771520,1966080,7710,1973790,14745600,14745600,2566914048,4278216192,2566940160,2566914048,1711276032,0,510001152,510001152,0,0,0,0,0,0,0,0,255,255,0,0,16711680,65280,16776960,16711680,16711680,0,0,0,0,0,0,4294901760,4294901760,0,0]
private def targetMask : Fin 20 → ℕ := ![135,255,135,120,135,39168,65280,39168,39168,26112,0,1966080,1966080,0,0,0,1711276032,1711276032,0,0]
private def combinationMask : Fin 20 → ℕ := ![8388610,2,8388610,8388608,8388610,276828168,8,276828168,276828168,276828160,0,134217728,134217728,0,0,0,5532286976,5532286976,0,0]
private def input (i : Fin 67) := binaryVectorOfMask 32 (inputMask i)
private def target (i : Fin 20) := binaryVectorOfMask 32 (targetMask i)
private def inputActual (i : Fin 67) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  if h : i.val < 12 then
    squareFunctional ⟨i.val / 3, by omega⟩ (binaryVectorOfMask 8 (annihilatorK13 ⟨i.val % 3, by omega⟩))
  else
    relatorFunctional ⟨(i.val - 12) / 5, by omega⟩ (binaryVectorOfMask 8 (annihilatorR13 ⟨(i.val - 12) % 5, by omega⟩))
private def targetActual (i : Fin 20) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  squareFunctional ⟨i.val / 5, by omega⟩ (binaryVectorOfMask 8 (annihilatorR13 ⟨i.val % 5, by omega⟩))
private theorem input_basis : ∀ i j,
  binaryRowFunctional (input i) (Pi.single j 1) = inputActual i (Pi.single j 1) := by decide +kernel
private theorem target_basis : ∀ i j,
  binaryRowFunctional (target i) (Pi.single j 1) = targetActual i (Pi.single j 1) := by decide +kernel
private def certificate : BinaryLinearConstraintCertificate input target where
  support j := Finset.univ.filter fun i => (combinationMask j).testBit i.val
  target_eq := by decide +kernel
theorem square_carry (x : Offsets) (hsquare : ∀ i, squareMap i x ∈ K13)
    (hrelator : ∀ r, relatorMap r x ∈ R13) : ∀ i, squareMap i x ∈ R13 := by
  have hinput (i : Fin 67) : dotProduct (input i) x = 0 := by
    change binaryRowFunctional (input i) x = 0
    rw [binaryLinearFunctional_ext_basis (input_basis i)]
    unfold inputActual
    split_ifs with h
    · have hs := hsquare (⟨i.val / 3, by omega⟩ : Fin 4)
      simp only [K13, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hs
      exact hs ⟨i.val % 3, by omega⟩
    · have hr := hrelator (⟨(i.val - 12) / 5, by omega⟩ : Fin 11)
      simp only [R13, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hr
      exact hr ⟨(i.val - 12) % 5, by omega⟩
  intro i
  simp only [R13, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro chi
  have ht := certificate.target_dotProduct_eq_zero x hinput (⟨5 * i.val + chi.val, by omega⟩ : Fin 20)
  change binaryRowFunctional (target _) x = 0 at ht
  rw [binaryLinearFunctional_ext_basis (target_basis _)] at ht
  have hd : (5 * i.val + chi.val) / 5 = i.val := by omega
  have hm : (5 * i.val + chi.val) % 5 = chi.val := by omega
  simpa only [targetActual, hd, hm] using ht

end SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry.Case13
