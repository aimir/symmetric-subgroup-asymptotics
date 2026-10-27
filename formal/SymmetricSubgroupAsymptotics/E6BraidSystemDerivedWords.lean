import SymmetricSubgroupAsymptotics.E6BraidSystemWordAlgebra
import SymmetricSubgroupAsymptotics.InvolutionEvenWordDerived
import Mathlib.Tactic.FinCases

/-! Selected E6 EVEN words lie in the ACTUAL ambient commutator. The
ambient six-involution family need not generate its ambient group, and
that group need not be finite or simple. This is designed for the actual
Bimonster node centralizer C, whose derived group is the Monster model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.E6BraidSystemDerivedWords
open InvolutionBraidTrace InvolutionBraidPresentation
open CFSGYE6SelectedWords (adjacent wordA wordB wordC)
open CFSGYE6RotationFirstConjugationBraidPilot (rotationWord)
open CFSGYE6FourierFirstConjugationBraidCertificate (fourierWord)
variable {G : Type*} [Group G] (S : System adjacent G)

private theorem cube_of_braid {K : Type*} [Group K] (x y : K)
    (hx : x*x=1) (hy : y*y=1) (hxy : x*y*x=y*x*y) : (x*y)^3=1 := by
  calc
    (x*y)^3=(x*y*x)*(y*x*y) := by simp only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc]
    _=(y*x*y)*(y*x*y) := by rw [hxy]
    _=y*x*(y*y)*x*y := by group
    _=y*(x*x)*y := by rw [hy]; group
    _=1 := by rw [hx,mul_one,hy]

 theorem abelianization_generators_equal (i : Fin 6) :
    Abelianization.of (S.generator i)=Abelianization.of (S.generator 0) := by
  have edge (j k : Fin 6) (hjk : adjacent j k=true) :
      Abelianization.of (S.generator j)=Abelianization.of (S.generator k) := by
    apply InvolutionEvenWordDerived.abelianization_eq_of_product_cube
    · simpa only [pow_two] using S.square j
    · simpa only [pow_two] using S.square k
    · exact cube_of_braid _ _ (S.square j) (S.square k) (S.braid j k hjk)
  fin_cases i
  · rfl
  · exact (edge 0 1 rfl).symm
  · exact ((edge 0 1 rfl).trans (edge 1 2 rfl)).symm
  · exact (edge 0 3 rfl).symm
  · exact ((edge 0 3 rfl).trans (edge 3 4 rfl)).symm
  · exact (edge 0 5 rfl).symm

 theorem even_value_mem_commutator (w : List (Fin 6)) (hlen : Even w.length) :
    value S.generator w∈commutator G :=
  InvolutionEvenWordDerived.value_mem_commutator S.generator 0
    (by simpa only [pow_two] using S.square 0) (abelianization_generators_equal S) w hlen

 def derivedWord (w : List (Fin 6)) (hlen : Even w.length) : commutator G :=
  ⟨value S.generator w,even_value_mem_commutator S w hlen⟩

 def a : commutator G := derivedWord S wordA (by decide)
 def b : commutator G := derivedWord S wordB (by decide)
 def c : commutator G := derivedWord S wordC (by decide)
 def r : commutator G := derivedWord S rotationWord (by decide)
 def q : commutator G := derivedWord S fourierWord (by decide)
 def firstInverter : commutator G := derivedWord S [1,3] (by decide)
 def secondInverter : commutator G := derivedWord S [1,5] (by decide)

 theorem a_cube : a S^3=1 := by
  apply Subtype.ext
  exact E6BraidSystemWordAlgebra.a_cube S
 theorem b_cube : b S^3=1 := by
  apply Subtype.ext
  exact E6BraidSystemWordAlgebra.b_cube S
 theorem c_cube : c S^3=1 := by
  apply Subtype.ext
  exact E6BraidSystemWordAlgebra.c_cube S
 theorem r_cube : r S^3=1 := by
  apply Subtype.ext
  exact E6BraidSystemWordAlgebra.r_cube S
 theorem a_commutes_b : Commute (a S) (b S) := by
  apply Subtype.ext
  exact (E6BraidSystemWordAlgebra.a_commutes_b S).eq
 theorem a_commutes_c : Commute (a S) (c S) := by
  apply Subtype.ext
  exact (E6BraidSystemWordAlgebra.a_commutes_c S).eq
 theorem b_commutes_c : Commute (b S) (c S) := by
  apply Subtype.ext
  exact (E6BraidSystemWordAlgebra.b_commutes_c S).eq
 theorem rotation_a : r S*a S*(r S)⁻¹=b S := by
  apply Subtype.ext
  exact E6BraidSystemWordAlgebra.rotation_a S
 theorem rotation_b : r S*b S*(r S)⁻¹=c S := by
  apply Subtype.ext
  exact E6BraidSystemWordAlgebra.rotation_b S
 theorem rotation_c : r S*c S*(r S)⁻¹=a S := by
  apply Subtype.ext
  exact E6BraidSystemWordAlgebra.rotation_c S
 theorem fourier_first : q S*(a S*(b S)⁻¹)*(q S)⁻¹=r S := by
  apply Subtype.ext
  exact E6BraidSystemWordAlgebra.fourier_first S
 theorem fourier_second : q S*r S*(q S)⁻¹=(a S*(b S)⁻¹)⁻¹ := by
  apply Subtype.ext
  exact E6BraidSystemWordAlgebra.fourier_second S

end SymmetricSubgroupAsymptotics.E6BraidSystemDerivedWords
