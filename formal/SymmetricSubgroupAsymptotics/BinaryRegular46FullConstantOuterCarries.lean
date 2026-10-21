import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare0
import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare1
import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare2
import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare3
import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare4
import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare5
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries
theorem target_zero (x : Offsets) (hx : ∀ i,dotProduct (input i) x=0)
    (i : Fin 6) (j : Fin 8) : dotProduct (target i j) x=0 := by
  fin_cases i
  · exact BinaryRegular46FullConstantOuterCarriesSquare0.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryRegular46FullConstantOuterCarriesSquare1.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryRegular46FullConstantOuterCarriesSquare2.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryRegular46FullConstantOuterCarriesSquare3.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryRegular46FullConstantOuterCarriesSquare4.certificate.target_dotProduct_eq_zero x hx j
  · exact BinaryRegular46FullConstantOuterCarriesSquare5.certificate.target_dotProduct_eq_zero x hx j

theorem square_carry (x : Offsets)
    (hsquare : ∀ i,squareMap i x ∈ wideState)
    (hrelator : ∀ r,relatorMap r x ∈ lowerRadical) :
    ∀ i,squareMap i x ∈ lowerRadical := by
  have hi (k : Fin 192) : dotProduct (input k) x=0 := by
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
end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries
