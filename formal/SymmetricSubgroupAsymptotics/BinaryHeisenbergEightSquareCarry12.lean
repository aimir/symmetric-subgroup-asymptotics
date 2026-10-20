import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarryData

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry.Case12

private def inputMask : Fin 37 → ℕ := ![0,0,0,0,255,65280,65535,0,0,0,0,4294901760,4294901760,16711680,16711680,0,4278190080,0,4278190080,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def targetMask : Fin 12 → ℕ := ![0,255,255,65280,0,65280,0,0,0,0,0,0]
private def combinationMask : Fin 12 → ℕ := ![0,16,16,32,0,32,0,0,0,0,0,0]
private def input (i : Fin 37) := binaryVectorOfMask 32 (inputMask i)
private def target (i : Fin 12) := binaryVectorOfMask 32 (targetMask i)
private def inputActual (i : Fin 37) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  if h : i.val < 4 then
    squareFunctional ⟨i.val / 1, by omega⟩ (binaryVectorOfMask 8 (annihilatorK12 ⟨i.val % 1, by omega⟩))
  else
    relatorFunctional ⟨(i.val - 4) / 3, by omega⟩ (binaryVectorOfMask 8 (annihilatorR12 ⟨(i.val - 4) % 3, by omega⟩))
private def targetActual (i : Fin 12) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  squareFunctional ⟨i.val / 3, by omega⟩ (binaryVectorOfMask 8 (annihilatorR12 ⟨i.val % 3, by omega⟩))
private theorem input_basis : ∀ i j,
  binaryRowFunctional (input i) (Pi.single j 1) = inputActual i (Pi.single j 1) := by decide +kernel
private theorem target_basis : ∀ i j,
  binaryRowFunctional (target i) (Pi.single j 1) = targetActual i (Pi.single j 1) := by decide +kernel
private def certificate : BinaryLinearConstraintCertificate input target where
  support j := Finset.univ.filter fun i => (combinationMask j).testBit i.val
  target_eq := by decide +kernel
theorem square_carry (x : Offsets) (hsquare : ∀ i, squareMap i x ∈ K12)
    (hrelator : ∀ r, relatorMap r x ∈ R12) : ∀ i, squareMap i x ∈ R12 := by
  have hinput (i : Fin 37) : dotProduct (input i) x = 0 := by
    change binaryRowFunctional (input i) x = 0
    rw [binaryLinearFunctional_ext_basis (input_basis i)]
    unfold inputActual
    split_ifs with h
    · have hs := hsquare (⟨i.val / 1, by omega⟩ : Fin 4)
      simp only [K12, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hs
      exact hs ⟨i.val % 1, by omega⟩
    · have hr := hrelator (⟨(i.val - 4) / 3, by omega⟩ : Fin 11)
      simp only [R12, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hr
      exact hr ⟨(i.val - 4) % 3, by omega⟩
  intro i
  simp only [R12, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro chi
  have ht := certificate.target_dotProduct_eq_zero x hinput (⟨3 * i.val + chi.val, by omega⟩ : Fin 12)
  change binaryRowFunctional (target _) x = 0 at ht
  rw [binaryLinearFunctional_ext_basis (target_basis _)] at ht
  have hd : (3 * i.val + chi.val) / 3 = i.val := by omega
  have hm : (3 * i.val + chi.val) % 3 = chi.val := by omega
  simpa only [targetActual, hd, hm] using ht

end SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarry.Case12
