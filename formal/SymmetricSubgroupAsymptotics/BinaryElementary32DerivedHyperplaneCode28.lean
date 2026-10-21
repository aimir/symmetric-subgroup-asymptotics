import SymmetricSubgroupAsymptotics.BinaryElementary32HyperplaneCertificate
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryElementary32DerivedHyperplaneCode28
local instance code28FactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BinaryElementary32FiniteCapacity
private def basisMasks : Fin 8 → ℕ := ![1,10,12,16,32,448,512,1024]
private def coordinateMasks : Fin 11 → ℕ := ![1,2,4,0,8,16,32,0,0,64,128]
private def inputMasks : Fin 4 → ℕ := ![14,384,320,272]
private def combinationMasks : Fin 11 → ℕ := ![0,0,0,1,0,0,0,6,4,0,0]
private def inclusion := (binaryRectangularMatrixOfColumnMasks 11 8 basisMasks).mulVecLin
private def coordinates := (binaryRectangularMatrixOfColumnMasks 8 11 coordinateMasks).mulVecLin
private theorem basis_left : ∀ i : Fin 8,coordinates (inclusion (Pi.single i 1))=Pi.single i 1 := by decide +kernel
private theorem left_inverse (v : Fin 8 → ZMod 2) : coordinates (inclusion v)=v := by
  have he : coordinates.comp inclusion=LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c=c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,basis_left,LinearMap.id_apply]
  exact DFunLike.congr_fun he v
private def chart : BinaryCoordinateSpace 11 8 := ⟨inclusion,coordinates,left_inverse⟩
private def input (i : Fin 4) := binaryVectorOfMask 11 (inputMasks i)
private def rowCertificate : BinaryLinearConstraintCertificate input (binaryCoordinateDefectRows chart) where
  support j := Finset.univ.filter fun i => (combinationMasks j).testBit i.val
  target_eq := by decide +kernel
private theorem input_basis : ∀ i : Fin 4,∀ j : Fin 11,
    binaryRowFunctional (input i) (Pi.single j 1)=hyperplaneInputFunctional 28 i (Pi.single j 1) := by decide +kernel
private abbrev H := binaryFiveHyperplane BinaryElementaryPhiZeroIntrinsicRadical.radical (28 : Fin 32)
private theorem allowed_test : ∀ i : Fin 16,
    (∀ j : Fin 11,BinaryElementary32DerivedHyperplaneOne.rowAction i (K.inclusion (Pi.single j 1))-
      K.inclusion (Pi.single j 1)∈H) → i∈({0} : Finset (Fin 16)) := by
  simp only [H,binaryFiveHyperplane,Submodule.mem_inf,LinearMap.mem_ker,BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem allowed_card_le : (allowedWords H).card≤2 := by
  have hsub : allowedWords H⊆({0} : Finset (Fin 16)) := by
    intro i hi
    exact allowed_test i (Finset.mem_filter.mp hi).2
  exact (Finset.card_le_card hsub).trans (by decide +kernel)
theorem capacity_le : capacity H≤512 := by
  have hf := hyperplane_fixed_card_le_of_certificate (28 : Fin 32) chart input rowCertificate
    (fun i => binaryLinearFunctional_ext_basis (input_basis i))
  exact (Nat.mul_le_mul hf allowed_card_le).trans (by norm_num)
end SymmetricSubgroupAsymptotics.BinaryElementary32DerivedHyperplaneCode28
