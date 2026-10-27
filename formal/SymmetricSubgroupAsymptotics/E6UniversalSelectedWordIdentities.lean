import SymmetricSubgroupAsymptotics.InvolutionBraidPresentation
import SymmetricSubgroupAsymptotics.CFSGYE6FirstConjugationBraidPilot
import SymmetricSubgroupAsymptotics.CFSGYE6SecondConjugationBraidPilot
import SymmetricSubgroupAsymptotics.CFSGYE6ThirdConjugationBraidPilot
import SymmetricSubgroupAsymptotics.CFSGYE6FourthConjugationBraidPilot
import SymmetricSubgroupAsymptotics.CFSGYE6RotationFirstConjugationBraidPilot
import SymmetricSubgroupAsymptotics.CFSGYE6RotationSecondConjugationBraidCertificate
import SymmetricSubgroupAsymptotics.CFSGYE6RotationCubeBraidCertificate
import SymmetricSubgroupAsymptotics.CFSGYE6FourierFirstConjugationBraidCertificate
import SymmetricSubgroupAsymptotics.CFSGYE6FourierSecondConjugationBraidCertificate

/-! All nine selected E6 word identities, proved from the SAME existing
Boolean braid certificates in the universal source, then transported to
ANY actual matching system. No Y spider relation or root-image identity
is used. Existing large trace lists are imported, never recopied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.E6UniversalSelectedWordIdentities
open InvolutionBraidTrace InvolutionBraidPresentation
open CFSGYE6SelectedWords (adjacent)

namespace FirstTheta

theorem universal_identity : value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FirstConjugationBraidPilot.start0=1 := by
  calc
    value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FirstConjugationBraidPilot.start0=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FirstConjugationBraidPilot.start1 :=
      universal_word_identity_of_check adjacent CFSGYE6FirstConjugationBraidPilot.start0 CFSGYE6FirstConjugationBraidPilot.trace0
        CFSGYE6FirstConjugationBraidPilot.start1 CFSGYE6FirstConjugationBraidPilot.certificate0
    _=1 := rfl

theorem identity_in_system {G : Type*} [Group G] (S : System adjacent G) :
    value S.generator CFSGYE6FirstConjugationBraidPilot.start0=1 := by
  have hh := congrArg (evaluation S) universal_identity
  rw [evaluation_value,map_one] at hh
  exact hh

end FirstTheta

namespace SecondTheta

theorem universal_identity : value (InvolutionBraidPresentation.generator adjacent) CFSGYE6SecondConjugationBraidPilot.start0=1 := by
  calc
    value (InvolutionBraidPresentation.generator adjacent) CFSGYE6SecondConjugationBraidPilot.start0=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6SecondConjugationBraidPilot.start1 :=
      universal_word_identity_of_check adjacent CFSGYE6SecondConjugationBraidPilot.start0 CFSGYE6SecondConjugationBraidPilot.trace0
        CFSGYE6SecondConjugationBraidPilot.start1 CFSGYE6SecondConjugationBraidPilot.certificate0
    _=1 := rfl

theorem identity_in_system {G : Type*} [Group G] (S : System adjacent G) :
    value S.generator CFSGYE6SecondConjugationBraidPilot.start0=1 := by
  have hh := congrArg (evaluation S) universal_identity
  rw [evaluation_value,map_one] at hh
  exact hh

end SecondTheta

namespace ThirdTheta

theorem universal_identity : value (InvolutionBraidPresentation.generator adjacent) CFSGYE6ThirdConjugationBraidPilot.start0=1 := by
  calc
    value (InvolutionBraidPresentation.generator adjacent) CFSGYE6ThirdConjugationBraidPilot.start0=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6ThirdConjugationBraidPilot.start1 :=
      universal_word_identity_of_check adjacent CFSGYE6ThirdConjugationBraidPilot.start0 CFSGYE6ThirdConjugationBraidPilot.trace0
        CFSGYE6ThirdConjugationBraidPilot.start1 CFSGYE6ThirdConjugationBraidPilot.certificate0
    _=1 := rfl

theorem identity_in_system {G : Type*} [Group G] (S : System adjacent G) :
    value S.generator CFSGYE6ThirdConjugationBraidPilot.start0=1 := by
  have hh := congrArg (evaluation S) universal_identity
  rw [evaluation_value,map_one] at hh
  exact hh

end ThirdTheta

namespace FourthTheta

theorem universal_identity : value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourthConjugationBraidPilot.start0=1 := by
  calc
    value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourthConjugationBraidPilot.start0=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourthConjugationBraidPilot.start1 :=
      universal_word_identity_of_check adjacent CFSGYE6FourthConjugationBraidPilot.start0 CFSGYE6FourthConjugationBraidPilot.trace0
        CFSGYE6FourthConjugationBraidPilot.start1 CFSGYE6FourthConjugationBraidPilot.certificate0
    _=1 := rfl

theorem identity_in_system {G : Type*} [Group G] (S : System adjacent G) :
    value S.generator CFSGYE6FourthConjugationBraidPilot.start0=1 := by
  have hh := congrArg (evaluation S) universal_identity
  rw [evaluation_value,map_one] at hh
  exact hh

end FourthTheta

namespace RotationFirst

theorem universal_identity : value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationFirstConjugationBraidPilot.start0=1 := by
  calc
    value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationFirstConjugationBraidPilot.start0=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationFirstConjugationBraidPilot.start1 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationFirstConjugationBraidPilot.start0 CFSGYE6RotationFirstConjugationBraidPilot.trace0
        CFSGYE6RotationFirstConjugationBraidPilot.start1 CFSGYE6RotationFirstConjugationBraidPilot.certificate0
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationFirstConjugationBraidPilot.start2 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationFirstConjugationBraidPilot.start1 CFSGYE6RotationFirstConjugationBraidPilot.trace1
        CFSGYE6RotationFirstConjugationBraidPilot.start2 CFSGYE6RotationFirstConjugationBraidPilot.certificate1
    _=1 := rfl

theorem identity_in_system {G : Type*} [Group G] (S : System adjacent G) :
    value S.generator CFSGYE6RotationFirstConjugationBraidPilot.start0=1 := by
  have hh := congrArg (evaluation S) universal_identity
  rw [evaluation_value,map_one] at hh
  exact hh

end RotationFirst

namespace RotationSecond

theorem universal_identity : value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationSecondConjugationBraidCertificate.start0=1 := by
  calc
    value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationSecondConjugationBraidCertificate.start0=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationSecondConjugationBraidCertificate.start1 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationSecondConjugationBraidCertificate.start0 CFSGYE6RotationSecondConjugationBraidCertificate.trace0
        CFSGYE6RotationSecondConjugationBraidCertificate.start1 CFSGYE6RotationSecondConjugationBraidCertificate.certificate0
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationSecondConjugationBraidCertificate.start2 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationSecondConjugationBraidCertificate.start1 CFSGYE6RotationSecondConjugationBraidCertificate.trace1
        CFSGYE6RotationSecondConjugationBraidCertificate.start2 CFSGYE6RotationSecondConjugationBraidCertificate.certificate1
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationSecondConjugationBraidCertificate.start3 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationSecondConjugationBraidCertificate.start2 CFSGYE6RotationSecondConjugationBraidCertificate.trace2
        CFSGYE6RotationSecondConjugationBraidCertificate.start3 CFSGYE6RotationSecondConjugationBraidCertificate.certificate2
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationSecondConjugationBraidCertificate.start4 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationSecondConjugationBraidCertificate.start3 CFSGYE6RotationSecondConjugationBraidCertificate.trace3
        CFSGYE6RotationSecondConjugationBraidCertificate.start4 CFSGYE6RotationSecondConjugationBraidCertificate.certificate3
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationSecondConjugationBraidCertificate.start5 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationSecondConjugationBraidCertificate.start4 CFSGYE6RotationSecondConjugationBraidCertificate.trace4
        CFSGYE6RotationSecondConjugationBraidCertificate.start5 CFSGYE6RotationSecondConjugationBraidCertificate.certificate4
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationSecondConjugationBraidCertificate.start6 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationSecondConjugationBraidCertificate.start5 CFSGYE6RotationSecondConjugationBraidCertificate.trace5
        CFSGYE6RotationSecondConjugationBraidCertificate.start6 CFSGYE6RotationSecondConjugationBraidCertificate.certificate5
    _=1 := rfl

theorem identity_in_system {G : Type*} [Group G] (S : System adjacent G) :
    value S.generator CFSGYE6RotationSecondConjugationBraidCertificate.start0=1 := by
  have hh := congrArg (evaluation S) universal_identity
  rw [evaluation_value,map_one] at hh
  exact hh

end RotationSecond

namespace RotationCube

theorem universal_identity : value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationCubeBraidCertificate.start0=1 := by
  calc
    value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationCubeBraidCertificate.start0=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationCubeBraidCertificate.start1 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationCubeBraidCertificate.start0 CFSGYE6RotationCubeBraidCertificate.trace0
        CFSGYE6RotationCubeBraidCertificate.start1 CFSGYE6RotationCubeBraidCertificate.certificate0
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationCubeBraidCertificate.start2 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationCubeBraidCertificate.start1 CFSGYE6RotationCubeBraidCertificate.trace1
        CFSGYE6RotationCubeBraidCertificate.start2 CFSGYE6RotationCubeBraidCertificate.certificate1
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationCubeBraidCertificate.start3 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationCubeBraidCertificate.start2 CFSGYE6RotationCubeBraidCertificate.trace2
        CFSGYE6RotationCubeBraidCertificate.start3 CFSGYE6RotationCubeBraidCertificate.certificate2
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationCubeBraidCertificate.start4 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationCubeBraidCertificate.start3 CFSGYE6RotationCubeBraidCertificate.trace3
        CFSGYE6RotationCubeBraidCertificate.start4 CFSGYE6RotationCubeBraidCertificate.certificate3
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6RotationCubeBraidCertificate.start5 :=
      universal_word_identity_of_check adjacent CFSGYE6RotationCubeBraidCertificate.start4 CFSGYE6RotationCubeBraidCertificate.trace4
        CFSGYE6RotationCubeBraidCertificate.start5 CFSGYE6RotationCubeBraidCertificate.certificate4
    _=1 := rfl

theorem identity_in_system {G : Type*} [Group G] (S : System adjacent G) :
    value S.generator CFSGYE6RotationCubeBraidCertificate.start0=1 := by
  have hh := congrArg (evaluation S) universal_identity
  rw [evaluation_value,map_one] at hh
  exact hh

end RotationCube

namespace FourierFirst

theorem universal_identity : value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierFirstConjugationBraidCertificate.start0=1 := by
  calc
    value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierFirstConjugationBraidCertificate.start0=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierFirstConjugationBraidCertificate.start1 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierFirstConjugationBraidCertificate.start0 CFSGYE6FourierFirstConjugationBraidCertificate.trace0
        CFSGYE6FourierFirstConjugationBraidCertificate.start1 CFSGYE6FourierFirstConjugationBraidCertificate.certificate0
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierFirstConjugationBraidCertificate.start2 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierFirstConjugationBraidCertificate.start1 CFSGYE6FourierFirstConjugationBraidCertificate.trace1
        CFSGYE6FourierFirstConjugationBraidCertificate.start2 CFSGYE6FourierFirstConjugationBraidCertificate.certificate1
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierFirstConjugationBraidCertificate.start3 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierFirstConjugationBraidCertificate.start2 CFSGYE6FourierFirstConjugationBraidCertificate.trace2
        CFSGYE6FourierFirstConjugationBraidCertificate.start3 CFSGYE6FourierFirstConjugationBraidCertificate.certificate2
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierFirstConjugationBraidCertificate.start4 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierFirstConjugationBraidCertificate.start3 CFSGYE6FourierFirstConjugationBraidCertificate.trace3
        CFSGYE6FourierFirstConjugationBraidCertificate.start4 CFSGYE6FourierFirstConjugationBraidCertificate.certificate3
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierFirstConjugationBraidCertificate.start5 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierFirstConjugationBraidCertificate.start4 CFSGYE6FourierFirstConjugationBraidCertificate.trace4
        CFSGYE6FourierFirstConjugationBraidCertificate.start5 CFSGYE6FourierFirstConjugationBraidCertificate.certificate4
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierFirstConjugationBraidCertificate.start6 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierFirstConjugationBraidCertificate.start5 CFSGYE6FourierFirstConjugationBraidCertificate.trace5
        CFSGYE6FourierFirstConjugationBraidCertificate.start6 CFSGYE6FourierFirstConjugationBraidCertificate.certificate5
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierFirstConjugationBraidCertificate.start7 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierFirstConjugationBraidCertificate.start6 CFSGYE6FourierFirstConjugationBraidCertificate.trace6
        CFSGYE6FourierFirstConjugationBraidCertificate.start7 CFSGYE6FourierFirstConjugationBraidCertificate.certificate6
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierFirstConjugationBraidCertificate.start8 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierFirstConjugationBraidCertificate.start7 CFSGYE6FourierFirstConjugationBraidCertificate.trace7
        CFSGYE6FourierFirstConjugationBraidCertificate.start8 CFSGYE6FourierFirstConjugationBraidCertificate.certificate7
    _=1 := rfl

theorem identity_in_system {G : Type*} [Group G] (S : System adjacent G) :
    value S.generator CFSGYE6FourierFirstConjugationBraidCertificate.start0=1 := by
  have hh := congrArg (evaluation S) universal_identity
  rw [evaluation_value,map_one] at hh
  exact hh

end FourierFirst

namespace FourierSecond

theorem universal_identity : value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierSecondConjugationBraidCertificate.start0=1 := by
  calc
    value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierSecondConjugationBraidCertificate.start0=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierSecondConjugationBraidCertificate.start1 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierSecondConjugationBraidCertificate.start0 CFSGYE6FourierSecondConjugationBraidCertificate.trace0
        CFSGYE6FourierSecondConjugationBraidCertificate.start1 CFSGYE6FourierSecondConjugationBraidCertificate.certificate0
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierSecondConjugationBraidCertificate.start2 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierSecondConjugationBraidCertificate.start1 CFSGYE6FourierSecondConjugationBraidCertificate.trace1
        CFSGYE6FourierSecondConjugationBraidCertificate.start2 CFSGYE6FourierSecondConjugationBraidCertificate.certificate1
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierSecondConjugationBraidCertificate.start3 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierSecondConjugationBraidCertificate.start2 CFSGYE6FourierSecondConjugationBraidCertificate.trace2
        CFSGYE6FourierSecondConjugationBraidCertificate.start3 CFSGYE6FourierSecondConjugationBraidCertificate.certificate2
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierSecondConjugationBraidCertificate.start4 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierSecondConjugationBraidCertificate.start3 CFSGYE6FourierSecondConjugationBraidCertificate.trace3
        CFSGYE6FourierSecondConjugationBraidCertificate.start4 CFSGYE6FourierSecondConjugationBraidCertificate.certificate3
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierSecondConjugationBraidCertificate.start5 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierSecondConjugationBraidCertificate.start4 CFSGYE6FourierSecondConjugationBraidCertificate.trace4
        CFSGYE6FourierSecondConjugationBraidCertificate.start5 CFSGYE6FourierSecondConjugationBraidCertificate.certificate4
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierSecondConjugationBraidCertificate.start6 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierSecondConjugationBraidCertificate.start5 CFSGYE6FourierSecondConjugationBraidCertificate.trace5
        CFSGYE6FourierSecondConjugationBraidCertificate.start6 CFSGYE6FourierSecondConjugationBraidCertificate.certificate5
    _=value (InvolutionBraidPresentation.generator adjacent) CFSGYE6FourierSecondConjugationBraidCertificate.start7 :=
      universal_word_identity_of_check adjacent CFSGYE6FourierSecondConjugationBraidCertificate.start6 CFSGYE6FourierSecondConjugationBraidCertificate.trace6
        CFSGYE6FourierSecondConjugationBraidCertificate.start7 CFSGYE6FourierSecondConjugationBraidCertificate.certificate6
    _=1 := rfl

theorem identity_in_system {G : Type*} [Group G] (S : System adjacent G) :
    value S.generator CFSGYE6FourierSecondConjugationBraidCertificate.start0=1 := by
  have hh := congrArg (evaluation S) universal_identity
  rw [evaluation_value,map_one] at hh
  exact hh

end FourierSecond

end SymmetricSubgroupAsymptotics.E6UniversalSelectedWordIdentities
