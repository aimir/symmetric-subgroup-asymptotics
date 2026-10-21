import SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare0
import SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare1
import SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare2
import SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare3
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarries
theorem target_zero (x : Offsets) (hx : ∀ i,dotProduct (input i) x=0)
    (i : Fin 4) (j : Fin 11) : dotProduct (target i j) x=0 := by
  fin_cases i
  · exact BinaryElementary16PhiZeroOuterCarriesSquare0.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryElementary16PhiZeroOuterCarriesSquare1.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryElementary16PhiZeroOuterCarriesSquare2.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryElementary16PhiZeroOuterCarriesSquare3.certificate.target_dotProduct_eq_zero x hx j

theorem square_carry (x : Offsets)
    (hsquare : ∀ i,squareMap i x ∈ wideState)
    (hrelator : ∀ r,relatorMap r x ∈ lowerRadical) :
    ∀ i,squareMap i x ∈ lowerRadical := by
  have hi (k : Fin 86) : dotProduct (input k) x=0 := by
    change binaryRowFunctional (input k) x=0
    rw [binaryLinearFunctional_ext_basis (input_basis k)]
    cases hsrc : inputSource k with
    | inl ij =>
      have hh := hsquare ij.1
      simp only [wideState,annihilatorSpace,Submodule.mem_iInf,LinearMap.mem_ker] at hh
      simpa only [inputActual,hsrc,LinearMap.comp_apply] using hh ij.2
    | inr ij =>
      have hh := hrelator ij.1
      simp only [lowerRadical,annihilatorSpace,Submodule.mem_iInf,LinearMap.mem_ker] at hh
      simpa only [inputActual,hsrc,LinearMap.comp_apply] using hh ij.2
  intro i
  simp only [lowerRadical,annihilatorSpace,Submodule.mem_iInf,LinearMap.mem_ker]
  intro j
  have hz := target_zero x hi i j
  change binaryRowFunctional (target i j) x=0 at hz
  rw [binaryLinearFunctional_ext_basis (target_basis i j)] at hz
  exact hz
end SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarries
