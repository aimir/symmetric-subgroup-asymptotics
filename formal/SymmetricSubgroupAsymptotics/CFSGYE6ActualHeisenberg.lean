import SymmetricSubgroupAsymptotics.CFSGYE6ActualTriple
import SymmetricSubgroupAsymptotics.TernaryThreeCycleHeisenberg
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Actual paired derived inverters certify the Heisenberg centre
nontrivial in the FULL Y derived-centre quotient. The resulting injective
homomorphism has no independence, recognition, finiteness or group-order
premise. Its only model input is inherited quotient noncommutativity.
This does not yet assert compatible Fourier/shear normalization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYE6ActualHeisenberg
open CFSG.Models.YGroups CFSGYE6SelectedWords CFSGYE6BraidCertificateConsumers
open CFSGYE6ActualTriple

private theorem pair_inverts {G : Type*} [Group G] (x y z : G)
    (hxx : x*x=1) (hyy : y*y=1) (hc : Commute z (x*y)) :
    (x*z)*(x*y)*(x*z)⁻¹=(x*y)⁻¹ := by
  have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right hxx
  have hj : y⁻¹=y := inv_eq_of_mul_eq_one_right hyy
  calc
    (x*z)*(x*y)*(x*z)⁻¹ = x*(z*(x*y))*z⁻¹*x⁻¹ := by group
    _ = x*((x*y)*z)*z⁻¹*x⁻¹ := by rw [hc.eq]
    _ = (x*x)*y*x⁻¹ := by group
    _ = y*x := by rw [hxx,one_mul,hi]
    _ = (x*y)⁻¹ := by rw [mul_inv_rev,hi,hj]

private theorem conjugation_fixed {G : Type*} [Group G] (x y : G) (hc : Commute x y) :
    x*y*x⁻¹=y := by rw [hc.eq]; group

def derivedFirstInverter (arms : Arms) : Derived arms := derivedWord arms [1,3] (by decide)
def derivedSecondInverter (arms : Arms) : Derived arms := derivedWord arms [1,5] (by decide)

private theorem derived_first_a (arms : Arms) :
    derivedFirstInverter arms*derivedA arms*(derivedFirstInverter arms)⁻¹=(derivedA arms)⁻¹ := by
  apply Subtype.ext
  change eval arms [1,3]*eval arms wordA*(eval arms [1,3])⁻¹=(eval arms wordA)⁻¹
  simp only [eval_pair,raw_a]
  exact pair_inverts _ _ _ (generator_square arms 1) (generator_square arms 2)
    ((generator_commutes arms 3 1 rfl).mul_right (generator_commutes arms 3 2 rfl))

private theorem derived_first_b (arms : Arms) :
    derivedFirstInverter arms*derivedB arms*(derivedFirstInverter arms)⁻¹=(derivedB arms)⁻¹ := by
  apply Subtype.ext
  change eval arms [1,3]*eval arms wordB*(eval arms [1,3])⁻¹=(eval arms wordB)⁻¹
  simp only [eval_pair,raw_b,(generator_commutes arms 1 3 rfl).eq]
  exact pair_inverts _ _ _ (generator_square arms 3) (generator_square arms 4)
    ((generator_commutes arms 1 3 rfl).mul_right (generator_commutes arms 1 4 rfl))

private theorem derived_first_c (arms : Arms) :
    derivedFirstInverter arms*derivedC arms*(derivedFirstInverter arms)⁻¹=derivedC arms := by
  apply Subtype.ext
  change eval arms [1,3]*eval arms wordC*(eval arms [1,3])⁻¹=eval arms wordC
  simp only [eval_pair]
  exact conjugation_fixed _ _ ((first_commutes_c arms).mul_left (third_commutes_c arms))

private theorem derived_second_a (arms : Arms) :
    derivedSecondInverter arms*derivedA arms*(derivedSecondInverter arms)⁻¹=(derivedA arms)⁻¹ := by
  apply Subtype.ext
  change eval arms [1,5]*eval arms wordA*(eval arms [1,5])⁻¹=(eval arms wordA)⁻¹
  simp only [eval_pair,raw_a]
  exact pair_inverts _ _ _ (generator_square arms 1) (generator_square arms 2)
    ((generator_commutes arms 5 1 rfl).mul_right (generator_commutes arms 5 2 rfl))

private theorem derived_second_b (arms : Arms) :
    derivedSecondInverter arms*derivedB arms*(derivedSecondInverter arms)⁻¹=derivedB arms := by
  have h1 : Commute (generator arms 1) (eval arms wordB) := by
    rw [raw_b]
    exact (generator_commutes arms 1 3 rfl).mul_right (generator_commutes arms 1 4 rfl)
  have h5 : Commute (generator arms 5) (eval arms wordB) := by
    rw [raw_b]
    exact (generator_commutes arms 5 3 rfl).mul_right (generator_commutes arms 5 4 rfl)
  apply Subtype.ext
  change eval arms [1,5]*eval arms wordB*(eval arms [1,5])⁻¹=eval arms wordB
  simp only [eval_pair]
  exact conjugation_fixed _ _ (h1.mul_left h5)

private theorem derived_second_c (arms : Arms) :
    derivedSecondInverter arms*derivedC arms*(derivedSecondInverter arms)⁻¹=(derivedC arms)⁻¹ := by
  apply Subtype.ext
  change eval arms [1,5]*eval arms wordC*(eval arms [1,5])⁻¹=(eval arms wordC)⁻¹
  simp only [eval_pair,raw_c,(generator_commutes arms 1 5 rfl).eq]
  exact pair_inverts _ _ _ (generator_square arms 5)
    (by simpa only [pow_two] using theta_square arms)
    ((generator_commutes arms 1 5 rfl).mul_right
      (CFSGYE6FirstThetaCommutation.theta_commutes_first arms))

def firstInverter (arms : Arms) : SimpleSection arms := quotient arms (derivedFirstInverter arms)
def secondInverter (arms : Arms) : SimpleSection arms := quotient arms (derivedSecondInverter arms)

theorem first_a (arms : Arms) : firstInverter arms*a arms*(firstInverter arms)⁻¹=(a arms)⁻¹ := by
  have h := congrArg (quotient arms) (derived_first_a arms)
  simpa only [map_mul,map_inv] using h

theorem first_b (arms : Arms) : firstInverter arms*b arms*(firstInverter arms)⁻¹=(b arms)⁻¹ := by
  have h := congrArg (quotient arms) (derived_first_b arms)
  simpa only [map_mul,map_inv] using h

theorem first_c (arms : Arms) : firstInverter arms*c arms*(firstInverter arms)⁻¹=c arms := by
  have h := congrArg (quotient arms) (derived_first_c arms)
  simpa only [map_mul,map_inv] using h

theorem second_a (arms : Arms) : secondInverter arms*a arms*(secondInverter arms)⁻¹=(a arms)⁻¹ := by
  have h := congrArg (quotient arms) (derived_second_a arms)
  simpa only [map_mul,map_inv] using h

theorem second_b (arms : Arms) : secondInverter arms*b arms*(secondInverter arms)⁻¹=b arms := by
  have h := congrArg (quotient arms) (derived_second_b arms)
  simpa only [map_mul,map_inv] using h

theorem second_c (arms : Arms) : secondInverter arms*c arms*(secondInverter arms)⁻¹=(c arms)⁻¹ := by
  have h := congrArg (quotient arms) (derived_second_c arms)
  simpa only [map_mul,map_inv] using h

def firstConjugation (arms : Arms) : SimpleSection arms →* SimpleSection arms :=
  (MulAut.conj (firstInverter arms)).toMonoidHom

def secondConjugation (arms : Arms) : SimpleSection arms →* SimpleSection arms :=
  (MulAut.conj (secondInverter arms)).toMonoidHom

def hom (arms : Arms) : CFSGHeisenbergCoordinateGroup.Element (ZMod 3) 1 →* SimpleSection arms :=
  TernaryThreeCycleHeisenberg.hom (a arms) (b arms) (c arms) (r arms)
    (a_cube arms) (b_cube arms) (c_cube arms) (r_cube arms)
    (a_commutes_b arms) (a_commutes_c arms) (b_commutes_c arms)
    (rotation_a arms) (rotation_b arms) (rotation_c arms)

theorem diagonal_ne_one (arms : Arms) (hn : ¬IsMulCommutative (SimpleSection arms)) :
    TernaryThreeCycleHeisenberg.diagonal (a arms) (b arms) (c arms)≠1 :=
  TernaryThreeCycleHeisenberg.diagonal_ne_one (a arms) (b arms) (c arms)
    (firstConjugation arms) (secondConjugation arms)
    (a_cube arms) (b_cube arms) (c_cube arms)
    (a_commutes_b arms) (a_commutes_c arms) (b_commutes_c arms)
    (first_a arms) (first_b arms) (first_c arms)
    (second_a arms) (second_b arms) (second_c arms) (a_ne_one arms hn)

theorem hom_injective (arms : Arms) (hn : ¬IsMulCommutative (SimpleSection arms)) :
    Function.Injective (hom arms) :=
  TernaryThreeCycleHeisenberg.hom_injective (a arms) (b arms) (c arms) (r arms)
    (firstConjugation arms) (secondConjugation arms)
    (a_cube arms) (b_cube arms) (c_cube arms) (r_cube arms)
    (a_commutes_b arms) (a_commutes_c arms) (b_commutes_c arms)
    (rotation_a arms) (rotation_b arms) (rotation_c arms)
    (first_a arms) (first_b arms) (first_c arms)
    (second_a arms) (second_b arms) (second_c arms) (a_ne_one arms hn)

end SymmetricSubgroupAsymptotics.CFSGYE6ActualHeisenberg
