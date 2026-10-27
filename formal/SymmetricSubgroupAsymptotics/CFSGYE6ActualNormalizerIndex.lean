import SymmetricSubgroupAsymptotics.CFSGYE6ActualHeisenberg
import SymmetricSubgroupAsymptotics.CFSGYE6FourierFirstConjugationBraidCertificate
import SymmetricSubgroupAsymptotics.CFSGYE6FourierSecondConjugationBraidCertificate
import SymmetricSubgroupAsymptotics.TernaryHeisenbergGeneratorNormalizer

/-! Compatible rotation and shear in the SAME actual full derived-centre
Y quotient. Both Fourier conjugations are literal braid certificates;
the central relation and lower shear then follow algebraically. The
Heisenberg injection retains inherited noncommutativity, and proper
index27 retains only inherited finiteness and simplicity. There is no
recognition, order, independence or normalization callback. This concerns
the full Y section, not the Monster derived involution-centralizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYE6ActualNormalizerIndex
open CFSG.Models.YGroups CFSGYE6SelectedWords CFSGYE6ActualTriple
open CFSGYE6RotationFirstConjugationBraidPilot (rotationWord)

abbrev x (arms : Arms) : SimpleSection arms :=
  TernaryThreeCycleHeisenberg.difference (a arms) (b arms)
abbrev z (arms : Arms) : SimpleSection arms :=
  TernaryThreeCycleHeisenberg.diagonal (a arms) (b arms) (c arms)

def derivedFourier (arms : Arms) : Derived arms :=
  derivedWord arms CFSGYE6FourierFirstConjugationBraidCertificate.fourierWord (by decide)

def q (arms : Arms) : SimpleSection arms := quotient arms (derivedFourier arms)
def lower (arms : Arms) : SimpleSection arms :=
  TernaryHeisenbergGeneratorNormalizer.lowerWord (q arms) (a arms)

theorem derived_fourier_first (arms : Arms) :
    derivedFourier arms*(derivedA arms*(derivedB arms)⁻¹)*(derivedFourier arms)⁻¹=
      derivedRotation arms := by
  apply Subtype.ext
  change eval arms CFSGYE6FourierFirstConjugationBraidCertificate.fourierWord*
    (eval arms wordA*(eval arms wordB)⁻¹)*
    (eval arms CFSGYE6FourierFirstConjugationBraidCertificate.fourierWord)⁻¹=
      eval arms rotationWord
  have h := CFSGYE6FourierFirstConjugationBraidCertificate.actual_conjugation arms
  rw [CFSGYE6FourierFirstConjugationBraidCertificate.difference_description] at h
  exact h

theorem derived_fourier_second (arms : Arms) :
    derivedFourier arms*derivedRotation arms*(derivedFourier arms)⁻¹=
      (derivedA arms*(derivedB arms)⁻¹)⁻¹ := by
  apply Subtype.ext
  change eval arms CFSGYE6FourierSecondConjugationBraidCertificate.fourierWord*
    eval arms rotationWord*
    (eval arms CFSGYE6FourierSecondConjugationBraidCertificate.fourierWord)⁻¹=
      (eval arms wordA*(eval arms wordB)⁻¹)⁻¹
  have h := CFSGYE6FourierSecondConjugationBraidCertificate.actual_conjugation arms
  rw [CFSGYE6FourierSecondConjugationBraidCertificate.difference_description] at h
  exact h

theorem fourier_first (arms : Arms) : q arms*x arms*(q arms)⁻¹=r arms := by
  have h := congrArg (quotient arms) (derived_fourier_first arms)
  simpa only [map_mul,map_inv] using h

theorem fourier_second (arms : Arms) : q arms*r arms*(q arms)⁻¹=(x arms)⁻¹ := by
  have h := congrArg (quotient arms) (derived_fourier_second arms)
  simpa only [map_mul,map_inv] using h

theorem fourier_third (arms : Arms) : q arms*z arms*(q arms)⁻¹=z arms :=
  TernaryHeisenbergGeneratorNormalizer.central_fixed_of_fourier (x arms) (r arms) (z arms)
    (q arms)
    (TernaryThreeCycleHeisenberg.difference_commute_diagonal _ _ _
      (a_commutes_b arms) (a_commutes_c arms) (b_commutes_c arms))
    (TernaryThreeCycleHeisenberg.collecting_relation _ _ _ _ (b_cube arms)
      (a_commutes_b arms) (a_commutes_c arms)
      (rotation_a arms) (rotation_b arms) (rotation_c arms))
    (fourier_first arms) (fourier_second arms)

theorem root_first (arms : Arms) : a arms*x arms*(a arms)⁻¹=x arms :=
  TernaryThreeCycleHeisenberg.root_conjugates_difference _ _ (a_commutes_b arms)

theorem root_second (arms : Arms) : a arms*r arms*(a arms)⁻¹=x arms*r arms :=
  TernaryThreeCycleHeisenberg.root_conjugates_rotation _ _ _ (rotation_a arms)

theorem root_third (arms : Arms) : a arms*z arms*(a arms)⁻¹=z arms :=
  TernaryThreeCycleHeisenberg.root_conjugates_diagonal _ _ _
    (a_commutes_b arms) (a_commutes_c arms)

theorem lower_first (arms : Arms) : lower arms*x arms*(lower arms)⁻¹=x arms*r arms :=
  TernaryHeisenbergGeneratorNormalizer.lower_first _ _ _ _
    (root_first arms) (root_second arms) (fourier_first arms) (fourier_second arms)

theorem lower_second (arms : Arms) : lower arms*r arms*(lower arms)⁻¹=r arms :=
  TernaryHeisenbergGeneratorNormalizer.lower_second _ _ _ _
    (root_first arms) (fourier_first arms)

theorem lower_third (arms : Arms) : lower arms*z arms*(lower arms)⁻¹=z arms :=
  TernaryHeisenbergGeneratorNormalizer.lower_third _ _ _
    (root_third arms) (fourier_third arms)

theorem hom_first (arms : Arms) :
    CFSGYE6ActualHeisenberg.hom arms TernaryHeisenbergGeneratorExt.first=x arms := by
  unfold CFSGYE6ActualHeisenberg.hom TernaryThreeCycleHeisenberg.hom
  exact TernaryHeisenbergGeneratorExt.hom_first _ _ _ _ _ _ _ _ _

theorem hom_second (arms : Arms) :
    CFSGYE6ActualHeisenberg.hom arms TernaryHeisenbergGeneratorExt.second=r arms := by
  unfold CFSGYE6ActualHeisenberg.hom TernaryThreeCycleHeisenberg.hom
  exact TernaryHeisenbergGeneratorExt.hom_second _ _ _ _ _ _ _ _ _

theorem hom_third (arms : Arms) :
    CFSGYE6ActualHeisenberg.hom arms TernaryHeisenbergGeneratorExt.third=z arms := by
  unfold CFSGYE6ActualHeisenberg.hom TernaryThreeCycleHeisenberg.hom
  exact TernaryHeisenbergGeneratorExt.hom_third _ _ _ _ _ _ _ _ _

theorem rotation_normalizes (arms : Arms) : ∀ h,
    q arms*CFSGYE6ActualHeisenberg.hom arms h*(q arms)⁻¹=
      CFSGYE6ActualHeisenberg.hom arms
        (QuaternaryPauliFourierPhaseNormalization.rotation h) := by
  apply TernaryHeisenbergGeneratorNormalizer.rotation_normalizes
  · simpa only [hom_first,hom_second] using fourier_first arms
  · simpa only [hom_first,hom_second] using fourier_second arms
  · simpa only [hom_third] using fourier_third arms

theorem shear_normalizes (arms : Arms) : ∀ h,
    lower arms*CFSGYE6ActualHeisenberg.hom arms h*(lower arms)⁻¹=
      CFSGYE6ActualHeisenberg.hom arms
        (QuaternaryPauliFourierPhaseNormalization.shear h) := by
  apply TernaryHeisenbergGeneratorNormalizer.shear_normalizes
  · simpa only [hom_first,hom_second] using lower_first arms
  · simpa only [hom_second] using lower_second arms
  · simpa only [hom_third] using lower_third arms

/-- Every proper subgroup of the actual full derived-centre Y quotient
has index at least27. No expected Fischer identification is used. -/
theorem proper_index_ge_twentySeven (arms : Arms) [Finite (SimpleSection arms)]
    [IsSimpleGroup (SimpleSection arms)] (hn : ¬IsMulCommutative (SimpleSection arms))
    (J : Subgroup (SimpleSection arms)) (hJ : J≠⊤) : 27≤J.index := by
  apply TernaryHeisenbergGeneratorNormalizer.proper_index_ge_twentySeven
    (CFSGYE6ActualHeisenberg.hom arms) (CFSGYE6ActualHeisenberg.hom_injective arms hn)
    (q arms) (lower arms)
  · simpa only [hom_first,hom_second] using fourier_first arms
  · simpa only [hom_first,hom_second] using fourier_second arms
  · simpa only [hom_third] using fourier_third arms
  · simpa only [hom_first,hom_second] using lower_first arms
  · simpa only [hom_second] using lower_second arms
  · simpa only [hom_third] using lower_third arms
  · exact hJ

end SymmetricSubgroupAsymptotics.CFSGYE6ActualNormalizerIndex
