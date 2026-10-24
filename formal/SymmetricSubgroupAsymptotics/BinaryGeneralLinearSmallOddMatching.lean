import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallPrimeSupport

/-! Literal odd-characteristic multiplicities in the small binary GL
orders. The finite check is seven integer orders on four prime supports;
it does not enumerate linear groups, subgroups or permutation actions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallOddMatching
open BinaryGeneralLinearSmallPrimeSupport BinaryGeneralLinearMatchingPrimeMultiplicity
open BinaryAffineJointSelectedWindowNumerics

theorem GL_odd_factorization_le_pred (d q : ℕ) (hd : d ≤ 6) (hq : q ≠ 2) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))).factorization q ≤ d-1 := by
  by_cases hmem : q ∈ ({2,3,5,7,31} : Finset ℕ)
  · have hmem' : q ∈ ({3,5,7,31} : Finset ℕ) := by
      simpa only [Finset.mem_insert,hq,false_or] using hmem
    have hh : ∀ k : Fin 7, ∀ p ∈ ({3,5,7,31} : Finset ℕ),
        (binaryGLOrder (k : ℕ)).factorization p ≤ (k : ℕ)-1 := by decide +kernel
    rw [matrix_GL_card_eq_order]
    exact hh ⟨d,by omega⟩ q hmem'
  · have hz := matchingMultiplicity_eq_zero d q hd hmem
    have hz' : (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))).factorization q = 0 := by
      simpa only [matchingMultiplicity,if_neg hq,add_zero] using hz
    rw [hz']
    exact Nat.zero_le _

theorem matchingMultiplicity_odd_le_pred (d q : ℕ) (hd : d ≤ 6) (hq : q ≠ 2) :
    matchingMultiplicity d q ≤ d-1 := by
  simpa only [matchingMultiplicity,if_neg hq,add_zero] using
    GL_odd_factorization_le_pred d q hd hq

end SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallOddMatching
