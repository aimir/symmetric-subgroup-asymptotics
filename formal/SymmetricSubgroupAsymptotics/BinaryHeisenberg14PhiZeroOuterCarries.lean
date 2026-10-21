import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesSquare0
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesSquare1
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesSquare2
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesSquare3
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesSquare4
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesSquare5
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarries
theorem target_zero (x : Offsets) (hx : ∀ i,dotProduct (input i) x=0)
    (i : Fin 6) (j : Fin 10) : dotProduct (target i j) x=0 := by
  fin_cases i
  · exact BinaryHeisenberg14PhiZeroOuterCarriesSquare0.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryHeisenberg14PhiZeroOuterCarriesSquare1.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryHeisenberg14PhiZeroOuterCarriesSquare2.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryHeisenberg14PhiZeroOuterCarriesSquare3.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryHeisenberg14PhiZeroOuterCarriesSquare4.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryHeisenberg14PhiZeroOuterCarriesSquare5.certificate.target_dotProduct_eq_zero x hx j

theorem square_carry (x : Offsets)
    (hsquare : ∀ i,squareMap i x ∈ wideState)
    (hrelator : ∀ r,relatorMap r x ∈ lowerRadical) :
    ∀ i,squareMap i x ∈ lowerRadical := by
  have hi (k : Fin 33) : dotProduct (input k) x=0 := by
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
end SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarries
