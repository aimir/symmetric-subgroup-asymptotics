import SymmetricSubgroupAsymptotics.E6BraidSystemDerivedWords
import SymmetricSubgroupAsymptotics.TernaryThreeCycleHeisenberg
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! A generic E6 involution system gives an injective Heisenberg27 in the
ACTUAL ambient commutator if its first selected adjacent cube is nontrivial.
All paired inverters are actual selected even words. No ambient finiteness,
generation, simplicity, full-Y quotient or root faithfulness is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.E6BraidSystemDerivedHeisenberg
open InvolutionBraidPresentation E6BraidSystemDerivedWords
open CFSGYE6SelectedWords (adjacent)
variable {G : Type*} [Group G] (S : System adjacent G)

private theorem pair_inverts {K : Type*} [Group K] (x y z : K)
    (hxx : x*x=1) (hyy : y*y=1) (hc : Commute z (x*y)) :
    (x*z)*(x*y)*(x*z)⁻¹=(x*y)⁻¹ := by
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right hxx
  have hj : y⁻¹=y := inv_eq_of_mul_eq_one_right hyy
  calc
    _=x*(z*(x*y))*z⁻¹*x⁻¹ := by group
    _=x*((x*y)*z)*z⁻¹*x⁻¹ := by rw [hc.eq]
    _=(x*x)*y*x⁻¹ := by group
    _=y*x := by rw [hxx,one_mul,hi]
    _=(x*y)⁻¹ := by rw [mul_inv_rev,hi,hj]

private theorem conjugation_fixed {K : Type*} [Group K] (x y : K) (hc : Commute x y) :
    x*y*x⁻¹=y := by rw [hc.eq]; group

 theorem first_a : firstInverter S*a S*(firstInverter S)⁻¹=(a S)⁻¹ := by
  apply Subtype.ext
  change E6BraidSystemWordAlgebra.eval S [1,3]*E6BraidSystemWordAlgebra.a S*
    (E6BraidSystemWordAlgebra.eval S [1,3])⁻¹=(E6BraidSystemWordAlgebra.a S)⁻¹
  simp only [E6BraidSystemWordAlgebra.eval_pair,E6BraidSystemWordAlgebra.raw_a]
  exact pair_inverts _ _ _ (S.square 1) (S.square 2)
    ((E6BraidSystemWordAlgebra.generator_commutes S 3 1 rfl).mul_right
      (E6BraidSystemWordAlgebra.generator_commutes S 3 2 rfl))

 theorem first_b : firstInverter S*b S*(firstInverter S)⁻¹=(b S)⁻¹ := by
  apply Subtype.ext
  change E6BraidSystemWordAlgebra.eval S [1,3]*E6BraidSystemWordAlgebra.b S*
    (E6BraidSystemWordAlgebra.eval S [1,3])⁻¹=(E6BraidSystemWordAlgebra.b S)⁻¹
  simp only [E6BraidSystemWordAlgebra.eval_pair,E6BraidSystemWordAlgebra.raw_b,
    (E6BraidSystemWordAlgebra.generator_commutes S 1 3 rfl).eq]
  exact pair_inverts _ _ _ (S.square 3) (S.square 4)
    ((E6BraidSystemWordAlgebra.generator_commutes S 1 3 rfl).mul_right
      (E6BraidSystemWordAlgebra.generator_commutes S 1 4 rfl))

 theorem first_c : firstInverter S*c S*(firstInverter S)⁻¹=c S := by
  apply Subtype.ext
  change E6BraidSystemWordAlgebra.eval S [1,3]*E6BraidSystemWordAlgebra.c S*
    (E6BraidSystemWordAlgebra.eval S [1,3])⁻¹=E6BraidSystemWordAlgebra.c S
  simp only [E6BraidSystemWordAlgebra.eval_pair]
  exact conjugation_fixed _ _ ((E6BraidSystemWordAlgebra.first_commutes_c S).mul_left
    (E6BraidSystemWordAlgebra.third_commutes_c S))

 theorem second_a : secondInverter S*a S*(secondInverter S)⁻¹=(a S)⁻¹ := by
  apply Subtype.ext
  change E6BraidSystemWordAlgebra.eval S [1,5]*E6BraidSystemWordAlgebra.a S*
    (E6BraidSystemWordAlgebra.eval S [1,5])⁻¹=(E6BraidSystemWordAlgebra.a S)⁻¹
  simp only [E6BraidSystemWordAlgebra.eval_pair,E6BraidSystemWordAlgebra.raw_a]
  exact pair_inverts _ _ _ (S.square 1) (S.square 2)
    ((E6BraidSystemWordAlgebra.generator_commutes S 5 1 rfl).mul_right
      (E6BraidSystemWordAlgebra.generator_commutes S 5 2 rfl))

 theorem second_b : secondInverter S*b S*(secondInverter S)⁻¹=b S := by
  have h1 : Commute (S.generator 1) (E6BraidSystemWordAlgebra.b S) := by
    rw [E6BraidSystemWordAlgebra.raw_b]
    exact (E6BraidSystemWordAlgebra.generator_commutes S 1 3 rfl).mul_right
      (E6BraidSystemWordAlgebra.generator_commutes S 1 4 rfl)
  have h5 : Commute (S.generator 5) (E6BraidSystemWordAlgebra.b S) := by
    rw [E6BraidSystemWordAlgebra.raw_b]
    exact (E6BraidSystemWordAlgebra.generator_commutes S 5 3 rfl).mul_right
      (E6BraidSystemWordAlgebra.generator_commutes S 5 4 rfl)
  apply Subtype.ext
  change E6BraidSystemWordAlgebra.eval S [1,5]*E6BraidSystemWordAlgebra.b S*
    (E6BraidSystemWordAlgebra.eval S [1,5])⁻¹=E6BraidSystemWordAlgebra.b S
  simp only [E6BraidSystemWordAlgebra.eval_pair]
  exact conjugation_fixed _ _ (h1.mul_left h5)

 theorem second_c : secondInverter S*c S*(secondInverter S)⁻¹=(c S)⁻¹ := by
  apply Subtype.ext
  change E6BraidSystemWordAlgebra.eval S [1,5]*E6BraidSystemWordAlgebra.c S*
    (E6BraidSystemWordAlgebra.eval S [1,5])⁻¹=(E6BraidSystemWordAlgebra.c S)⁻¹
  simp only [E6BraidSystemWordAlgebra.eval_pair,E6BraidSystemWordAlgebra.raw_c,
    (E6BraidSystemWordAlgebra.generator_commutes S 1 5 rfl).eq]
  exact pair_inverts _ _ _ (S.square 5)
    (by simpa only [pow_two] using E6BraidSystemWordAlgebra.theta_square S)
    ((E6BraidSystemWordAlgebra.generator_commutes S 1 5 rfl).mul_right
      (E6BraidSystemWordAlgebra.theta_commutes_one S))

 def firstConjugation : commutator G →* commutator G :=
  (MulAut.conj (firstInverter S)).toMonoidHom
 def secondConjugation : commutator G →* commutator G :=
  (MulAut.conj (secondInverter S)).toMonoidHom

 def hom : CFSGHeisenbergCoordinateGroup.Element (ZMod 3) 1 →* commutator G :=
  TernaryThreeCycleHeisenberg.hom (a S) (b S) (c S) (r S)
    (a_cube S) (b_cube S) (c_cube S) (r_cube S)
    (a_commutes_b S) (a_commutes_c S) (b_commutes_c S)
    (rotation_a S) (rotation_b S) (rotation_c S)

 theorem diagonal_ne_one (ha : a S≠1) :
    TernaryThreeCycleHeisenberg.diagonal (a S) (b S) (c S)≠1 :=
  TernaryThreeCycleHeisenberg.diagonal_ne_one (a S) (b S) (c S)
    (firstConjugation S) (secondConjugation S)
    (a_cube S) (b_cube S) (c_cube S)
    (a_commutes_b S) (a_commutes_c S) (b_commutes_c S)
    (first_a S) (first_b S) (first_c S)
    (second_a S) (second_b S) (second_c S) ha

 theorem hom_injective (ha : a S≠1) : Function.Injective (hom S) :=
  TernaryThreeCycleHeisenberg.hom_injective (a S) (b S) (c S) (r S)
    (firstConjugation S) (secondConjugation S)
    (a_cube S) (b_cube S) (c_cube S) (r_cube S)
    (a_commutes_b S) (a_commutes_c S) (b_commutes_c S)
    (rotation_a S) (rotation_b S) (rotation_c S)
    (first_a S) (first_b S) (first_c S)
    (second_a S) (second_b S) (second_c S) ha

end SymmetricSubgroupAsymptotics.E6BraidSystemDerivedHeisenberg
