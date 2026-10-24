import SymmetricSubgroupAsymptotics.OriginalBinaryAffineDominantDivisorCost
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallPrimeSupport

/-! Exact coefficients of the same actual binary GL order used by the
ordinary chief trace. Only seven integer orders and four odd prime
valuations are reduced. No linear groups, subgroups, actions or component
classification rows are enumerated. The translation head is included
in smallTotal and in the binary matching coefficient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallExactMultiplicities
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)
open BinaryGeneralLinearMatchingPrimeMultiplicity BinaryGeneralLinearSmallPrimeSupport
open BinaryAffineJointSelectedWindowNumerics

def smallTotal (d : ℕ) : ℕ :=
  match d with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 8
  | 4 => 14
  | 5 => 20
  | _ => 29

def smallOddMatching (d q : ℕ) : ℕ :=
  if q = 3 then
    if d ≤ 1 then 0 else if d ≤ 3 then 1 else if d ≤ 5 then 2 else 4
  else if q = 5 then if d ≤ 3 then 0 else 1
  else if q = 7 then if d ≤ 2 then 0 else if d ≤ 5 then 1 else 2
  else if q = 31 then if d ≤ 4 then 0 else 1
  else 0

theorem totalMultiplicity_eq (d : ℕ) (hd : d ≤ 6) : totalMultiplicity d = smallTotal d := by
  have hh : ∀ k : Fin 7, (k : ℕ)+ArithmeticFunction.cardFactors (binaryGLOrder k) =
      smallTotal k := by decide +kernel
  unfold totalMultiplicity
  rw [matrix_GL_card_eq_order]
  exact hh ⟨d,by omega⟩

theorem matching_two_eq (d : ℕ) : matchingMultiplicity d 2 = d+d*(d-1)/2 := by
  unfold matchingMultiplicity
  rw [PrimeGeneralLinearDefiningValuation.matrix_GL_defining_factorization 2 d Nat.prime_two]
  simp only [if_true]
  omega

theorem matching_odd_eq (d q : ℕ) (hd : d ≤ 6) (hq : q ≠ 2) :
    matchingMultiplicity d q = smallOddMatching d q := by
  by_cases hmem : q ∈ ({3,5,7,31} : Finset ℕ)
  · have hh : ∀ k : Fin 7, ∀ p ∈ ({3,5,7,31} : Finset ℕ),
        (binaryGLOrder k).factorization p = smallOddMatching k p := by decide +kernel
    rw [matchingMultiplicity,if_neg hq,add_zero,matrix_GL_card_eq_order]
    exact hh ⟨d,by omega⟩ q hmem
  · have hout : q ∉ ({2,3,5,7,31} : Finset ℕ) := by
      simpa only [Finset.mem_insert,hq,false_or] using hmem
    have hz := matchingMultiplicity_eq_zero d q hd hout
    have hn : q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 31 := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hmem
    rcases hn with ⟨h3,h5,h7,h31⟩
    rw [hz]
    simp only [smallOddMatching,if_neg h3,if_neg h5,if_neg h7,if_neg h31]

end SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallExactMultiplicities
