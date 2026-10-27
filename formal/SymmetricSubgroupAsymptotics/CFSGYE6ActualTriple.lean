import SymmetricSubgroupAsymptotics.CFSGYE6FirstThetaCommutation
import SymmetricSubgroupAsymptotics.CFSGYE6SecondConjugationBraidPilot
import SymmetricSubgroupAsymptotics.CFSGYE6ThirdConjugationBraidPilot
import SymmetricSubgroupAsymptotics.CFSGYE6FourthConjugationBraidPilot
import SymmetricSubgroupAsymptotics.CFSGYE6RotationCubeBraidCertificate
import SymmetricSubgroupAsymptotics.CFSGYE6RotationSecondConjugationBraidCertificate
import SymmetricSubgroupAsymptotics.CFSGYAdjacentDerivedNoncentral

/-! The ACTUAL selected E6 triple and cycler inside the original Y
derived group and its FULL centre quotient. The third cube is theta-C,
not the simple second node on arm2. All displayed word identities come
from the individually checked selected braid certificates. No order,
recognition, independent coordinates or new model premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYE6ActualTriple
open CFSG.Models.YGroups CFSGYE6SelectedWords CFSGYE6BraidCertificateConsumers
open CFSGYE6RotationFirstConjugationBraidPilot (rotationWord)

abbrev Derived (arms : Arms) := commutator (CFSG.Models.YGroups.Group arms)

theorem generator_commutes (arms : Arms) (i j : Fin 6) (hij : adjacent i j=false) :
    Commute (generator arms i) (generator arms j) := generator_commute arms i j hij

theorem eval_pair (arms : Arms) (i j : Fin 6) :
    eval arms [i,j]=generator arms i*generator arms j := by
  simp only [eval,InvolutionBraidTrace.value,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,mul_one]

theorem raw_a (arms : Arms) : eval arms wordA=generator arms 1*generator arms 2 :=
  eval_pair arms 1 2

theorem raw_b (arms : Arms) : eval arms wordB=generator arms 3*generator arms 4 :=
  eval_pair arms 3 4

theorem raw_c (arms : Arms) : eval arms wordC=generator arms 5*eval arms thetaWord := by
  change InvolutionBraidTrace.value (generator arms) ([5]++thetaWord)=_
  rw [InvolutionBraidTrace.value_append]
  simp only [InvolutionBraidTrace.value,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,mul_one]
  rfl

theorem theta_commutes_two (arms : Arms) :
    Commute (generator arms 2) (eval arms thetaWord) := by
  apply theta_commutes_of_identity arms 2 3 rfl
  rw [←CFSGYE6SecondConjugationBraidPilot.source_word]
  exact CFSGYE6SecondConjugationBraidPilot.selected_identity arms

theorem theta_commutes_three (arms : Arms) :
    Commute (generator arms 3) (eval arms thetaWord) := by
  apply theta_commutes_of_identity arms 3 2 rfl
  rw [←CFSGYE6ThirdConjugationBraidPilot.source_word]
  exact CFSGYE6ThirdConjugationBraidPilot.selected_identity arms

theorem theta_commutes_four (arms : Arms) :
    Commute (generator arms 4) (eval arms thetaWord) := by
  apply theta_commutes_of_identity arms 4 1 rfl
  rw [←CFSGYE6FourthConjugationBraidPilot.source_word]
  exact CFSGYE6FourthConjugationBraidPilot.selected_identity arms

theorem first_commutes_c (arms : Arms) :
    Commute (generator arms 1) (eval arms wordC) := by
  rw [raw_c]
  exact (generator_commutes arms 1 5 rfl).mul_right
    (CFSGYE6FirstThetaCommutation.theta_commutes_first arms)

theorem third_commutes_c (arms : Arms) :
    Commute (generator arms 3) (eval arms wordC) := by
  rw [raw_c]
  exact (generator_commutes arms 3 5 rfl).mul_right (theta_commutes_three arms)

theorem derived_a_commutes_c (arms : Arms) : Commute (derivedA arms) (derivedC arms) := by
  have h2 : Commute (generator arms 2) (eval arms wordC) := by
    rw [raw_c]
    exact (generator_commutes arms 2 5 rfl).mul_right (theta_commutes_two arms)
  apply Subtype.ext
  change eval arms wordA*eval arms wordC=eval arms wordC*eval arms wordA
  rw [raw_a]
  exact (first_commutes_c arms).mul_left h2

theorem derived_b_commutes_c (arms : Arms) : Commute (derivedB arms) (derivedC arms) := by
  have h4 : Commute (generator arms 4) (eval arms wordC) := by
    rw [raw_c]
    exact (generator_commutes arms 4 5 rfl).mul_right (theta_commutes_four arms)
  apply Subtype.ext
  change eval arms wordB*eval arms wordC=eval arms wordC*eval arms wordB
  rw [raw_b]
  exact (third_commutes_c arms).mul_left h4

def derivedRotation (arms : Arms) : Derived arms :=
  derivedWord arms rotationWord (by decide)

theorem derived_rotation_cube (arms : Arms) : derivedRotation arms ^ 3=1 := by
  apply Subtype.ext
  change eval arms rotationWord ^ 3=1
  exact CFSGYE6RotationCubeBraidCertificate.actual_cube arms

theorem derived_rotation_a (arms : Arms) :
    derivedRotation arms*derivedA arms*(derivedRotation arms)⁻¹=derivedB arms := by
  apply Subtype.ext
  change eval arms rotationWord*eval arms wordA*(eval arms rotationWord)⁻¹=eval arms wordB
  exact CFSGYE6RotationFirstConjugationBraidPilot.actual_conjugation arms

theorem derived_rotation_b (arms : Arms) :
    derivedRotation arms*derivedB arms*(derivedRotation arms)⁻¹=derivedC arms := by
  apply Subtype.ext
  change eval arms rotationWord*eval arms wordB*(eval arms rotationWord)⁻¹=eval arms wordC
  exact CFSGYE6RotationSecondConjugationBraidCertificate.actual_conjugation arms

private theorem cycle_third {G : Type*} [Group G] (r a b c : G) (hr : r^3=1)
    (ha : r*a*r⁻¹=b) (hb : r*b*r⁻¹=c) : r*c*r⁻¹=a := by
  calc
    r*c*r⁻¹ = r*(r*b*r⁻¹)*r⁻¹ := by rw [hb]
    _ = r*(r*(r*a*r⁻¹)*r⁻¹)*r⁻¹ := by rw [ha]
    _ = r^3*a*(r^3)⁻¹ := by
      simp only [pow_succ,pow_zero,mul_one]
      group
    _ = a := by rw [hr,inv_one,one_mul,mul_one]

private theorem cube_conjugate {G : Type*} [Group G] (r a b : G)
    (ha : a^3=1) (hb : r*a*r⁻¹=b) : b^3=1 := by
  calc
    b^3 = (r*a*r⁻¹)^3 := congrArg (fun z => z^3) hb.symm
    _ = r*(a^3)*r⁻¹ := by
      simp only [pow_succ,pow_zero,mul_one]
      group
    _ = 1 := by rw [ha]; group

theorem derived_rotation_c (arms : Arms) :
    derivedRotation arms*derivedC arms*(derivedRotation arms)⁻¹=derivedA arms :=
  cycle_third _ _ _ _ (derived_rotation_cube arms) (derived_rotation_a arms) (derived_rotation_b arms)

theorem derived_c_cube (arms : Arms) : derivedC arms ^ 3=1 :=
  cube_conjugate _ _ _ (derivedB_cube arms) (derived_rotation_b arms)

def quotient (arms : Arms) : Derived arms →* SimpleSection arms :=
  QuotientGroup.mk' (Subgroup.center (Derived arms))

def a (arms : Arms) : SimpleSection arms := quotient arms (derivedA arms)
def b (arms : Arms) : SimpleSection arms := quotient arms (derivedB arms)
def c (arms : Arms) : SimpleSection arms := quotient arms (derivedC arms)
def r (arms : Arms) : SimpleSection arms := quotient arms (derivedRotation arms)

theorem a_cube (arms : Arms) : a arms ^ 3=1 := by
  change (quotient arms (derivedA arms))^3=1
  rw [←map_pow,derivedA_cube,map_one]

theorem b_cube (arms : Arms) : b arms ^ 3=1 := by
  change (quotient arms (derivedB arms))^3=1
  rw [←map_pow,derivedB_cube,map_one]

theorem c_cube (arms : Arms) : c arms ^ 3=1 := by
  change (quotient arms (derivedC arms))^3=1
  rw [←map_pow,derived_c_cube,map_one]

theorem r_cube (arms : Arms) : r arms ^ 3=1 := by
  change (quotient arms (derivedRotation arms))^3=1
  rw [←map_pow,derived_rotation_cube,map_one]

theorem a_commutes_b (arms : Arms) : Commute (a arms) (b arms) := by
  have h := congrArg (quotient arms) (derivedA_commutes_derivedB arms).eq
  simpa only [map_mul] using h

theorem a_commutes_c (arms : Arms) : Commute (a arms) (c arms) := by
  have h := congrArg (quotient arms) (derived_a_commutes_c arms).eq
  simpa only [map_mul] using h

theorem b_commutes_c (arms : Arms) : Commute (b arms) (c arms) := by
  have h := congrArg (quotient arms) (derived_b_commutes_c arms).eq
  simpa only [map_mul] using h

theorem rotation_a (arms : Arms) : r arms*a arms*(r arms)⁻¹=b arms := by
  have h := congrArg (quotient arms) (derived_rotation_a arms)
  simpa only [map_mul,map_inv] using h

theorem rotation_b (arms : Arms) : r arms*b arms*(r arms)⁻¹=c arms := by
  have h := congrArg (quotient arms) (derived_rotation_b arms)
  simpa only [map_mul,map_inv] using h

theorem rotation_c (arms : Arms) : r arms*c arms*(r arms)⁻¹=a arms := by
  have h := congrArg (quotient arms) (derived_rotation_c arms)
  simpa only [map_mul,map_inv] using h

theorem a_ne_one (arms : Arms) (hn : ¬IsMulCommutative (SimpleSection arms)) : a arms≠1 := by
  have he : derivedA arms=CFSGYAdjacentDerivedNoncentral.armCube arms 0 := by
    apply Subtype.ext
    change eval arms wordA =
      CFSGYAdjacentDerivedNoncentral.generator arms (near arms 0 0)*
      CFSGYAdjacentDerivedNoncentral.generator arms (near arms 0 1)
    exact raw_a arms
  simpa only [a,quotient,he] using
    CFSGYAdjacentDerivedNoncentral.sectionArmCube_ne_one arms 0 hn

end SymmetricSubgroupAsymptotics.CFSGYE6ActualTriple
