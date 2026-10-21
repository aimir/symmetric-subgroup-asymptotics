import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare0
import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare1
import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare2
import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare3
import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare4
import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare5
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarries
theorem target_zero (x : Offsets) (hx : ∀ i, dotProduct (input i) x = 0)
    (i : Fin 6) (j : Fin 12) : dotProduct (target ⟨12 * i.val + j.val, by omega⟩) x = 0 := by
  fin_cases i
  · exact BinaryRegular46ParityZeroOuterCarriesSquare0.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryRegular46ParityZeroOuterCarriesSquare1.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryRegular46ParityZeroOuterCarriesSquare2.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryRegular46ParityZeroOuterCarriesSquare3.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryRegular46ParityZeroOuterCarriesSquare4.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryRegular46ParityZeroOuterCarriesSquare5.certificate.target_dotProduct_eq_zero x hx j

/-- Every original offset assignment obeying these literal square and
proved derived-word constraints has square carries in the same radical. -/
theorem square_carry (x : Offsets)
    (hsquare : ∀ i, squareMap i x ∈ wideState)
    (hrelator : ∀ r, relatorMap r x ∈ lowerRadical) :
    ∀ i, squareMap i x ∈ lowerRadical := by
  have hi (k : Fin 300) : dotProduct (input k) x = 0 := by
    change binaryRowFunctional (input k) x = 0
    rw [binaryLinearFunctional_ext_basis (input_basis k)]
    unfold inputActual
    split_ifs with h
    · have hh := hsquare (⟨k.val / 8, by omega⟩ : Fin 6)
      simp only [wideState, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hh
      exact hh ⟨k.val % 8, by omega⟩
    · have hh := hrelator (⟨(k.val - 48) / 12, by omega⟩ : Fin 21)
      simp only [lowerRadical, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hh
      exact hh ⟨(k.val - 48) % 12, by omega⟩
  intro i
  simp only [lowerRadical, annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro j
  have hz := target_zero x hi i j
  change binaryRowFunctional (target ⟨12 * i.val + j.val, by omega⟩) x = 0 at hz
  rw [binaryLinearFunctional_ext_basis (target_basis _)] at hz
  have hdiv : (12 * i.val + j.val) / 12 = i.val := by omega
  have hmod : (12 * i.val + j.val) % 12 = j.val := by omega
  simpa only [targetActual, hdiv, hmod] using hz
end SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarries
