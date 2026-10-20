import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchreierJointData
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow23Descriptor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow24Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow63Descriptor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairAverageNaturalFamily
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow64Descriptor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow65Descriptor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow66Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow68Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow96Descriptor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeBlockNaturalFamily
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow97Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow100Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow102Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow110Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow111Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow114Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow115Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow146Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow149Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow184Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow190Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow191Descriptor
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralRow227Descriptor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily

/-! Full joint clients from retained exact signed-S4 descriptors.
The common proof constructs every actual original quotient socle; the
natural-module fields are separately checked certificates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSignedS4JointClients
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open TwelvePointRemainingStructural

private theorem word_top {n : ℕ} {gs : Fin n → Equiv.Perm (Fin 12)}
    (D : SymmetricPairGeneratorData gs) (w : List (Fin n)) :
    D.frame.top ((w.map (closureGenerators gs)).prod)=D.topEmbedding ((w.map D.codes).prod) := by
  have hgen (i : Fin n) : D.frame.top (closureGenerators gs i)=D.topEmbedding (D.codes i) := by
    rw [← D.beta_action,D.beta_generator]
  induction w with
  | nil => simp only [List.map_nil,List.prod_nil,map_one]
  | cons i w ih =>
    simp only [List.map_cons,List.prod_cons,map_mul]
    rw [hgen,ih]

namespace Row23
private abbrev D := TwelvePointRemainingStructuralRow23Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow23Descriptor.schreierData
private def cubicWord : List (Fin 4) := [0,1,0]
private def cubic : Row23Top := (cubicWord.map (closureGenerators row23Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row23Interface :=
  C.jointDataAtTwo orbitCover row23Interface rfl PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row23Natural
end Row23

namespace Row24
private abbrev D := TwelvePointRemainingStructuralRow24Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow24Descriptor.schreierData
private def cubicWord : List (Fin 4) := [0,1,0]
private def cubic : Row24Top := (cubicWord.map (closureGenerators row24Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row24Interface :=
  C.jointDataAtTwo orbitCover row24Interface rfl PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row24Natural
end Row24

namespace Row63
private abbrev D := TwelvePointRemainingStructuralRow63Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow63Descriptor.schreierData
private def cubicWord : List (Fin 3) := [2,1,2,1,1]
private def cubic : Row63Top := (cubicWord.map (closureGenerators row63Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row63Interface :=
  C.jointDataAtTwo orbitCover row63Interface rfl PrimitiveAffineDegreeTwoTwelvePairAverageNaturalFamily.row63Natural
end Row63

namespace Row64
private abbrev D := TwelvePointRemainingStructuralRow64Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow64Descriptor.schreierData
private def cubicWord : List (Fin 3) := [2,1,2,1,1]
private def cubic : Row64Top := (cubicWord.map (closureGenerators row64Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row64Interface :=
  C.jointDataAtTwo orbitCover row64Interface rfl PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals.row64Natural
end Row64

namespace Row65
private abbrev D := TwelvePointRemainingStructuralRow65Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow65Descriptor.schreierData
private def cubicWord : List (Fin 4) := [3,1,2]
private def cubic : Row65Top := (cubicWord.map (closureGenerators row65Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row65Interface :=
  C.jointDataAtTwo orbitCover row65Interface rfl PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily.row65Natural
end Row65

namespace Row66
private abbrev D := TwelvePointRemainingStructuralRow66Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow66Descriptor.schreierData
private def cubicWord : List (Fin 4) := [1,1,2]
private def cubic : Row66Top := (cubicWord.map (closureGenerators row66Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row66Interface :=
  C.jointDataAtTwo orbitCover row66Interface rfl PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals.row66Natural
end Row66

namespace Row68
private abbrev D := TwelvePointRemainingStructuralRow68Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow68Descriptor.schreierData
private def cubicWord : List (Fin 4) := [1,2,1]
private def cubic : Row68Top := (cubicWord.map (closureGenerators row68Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row68Interface :=
  C.jointDataAtTwo orbitCover row68Interface rfl PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily.row68Natural
end Row68

namespace Row96
private abbrev D := TwelvePointRemainingStructuralRow96Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow96Descriptor.schreierData
private def cubicWord : List (Fin 3) := [1,2,1,1,2]
private def cubic : Row96Top := (cubicWord.map (closureGenerators row96Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,1]
private def orbitIndex : Fin 6 → Fin 2 := ![0,1,0,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,0,2,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row96Interface :=
  C.jointDataAtTwo orbitCover row96Interface rfl DegreeTwoTwelveThreeBlockNaturalFamily.row96Natural
end Row96

namespace Row97
private abbrev D := TwelvePointRemainingStructuralRow97Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow97Descriptor.schreierData
private def cubicWord : List (Fin 3) := [1,2,1,1,2]
private def cubic : Row97Top := (cubicWord.map (closureGenerators row97Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,1]
private def orbitIndex : Fin 6 → Fin 2 := ![0,1,0,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,0,2,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row97Interface :=
  C.jointDataAtTwo orbitCover row97Interface rfl DegreeTwoTwelveThreeBlockNaturalFamily.row97Natural
end Row97

namespace Row100
private abbrev D := TwelvePointRemainingStructuralRow100Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow100Descriptor.schreierData
private def cubicWord : List (Fin 4) := [1,2]
private def cubic : Row100Top := (cubicWord.map (closureGenerators row100Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,1]
private def orbitIndex : Fin 6 → Fin 2 := ![0,1,0,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,0,2,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row100Interface :=
  C.jointDataAtTwo orbitCover row100Interface rfl DegreeTwoTwelveThreeBlockNaturalFamily.row100Natural
end Row100

namespace Row102
private abbrev D := TwelvePointRemainingStructuralRow102Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow102Descriptor.schreierData
private def cubicWord : List (Fin 4) := [1,2]
private def cubic : Row102Top := (cubicWord.map (closureGenerators row102Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,1]
private def orbitIndex : Fin 6 → Fin 2 := ![0,1,0,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,0,2,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row102Interface :=
  C.jointDataAtTwo orbitCover row102Interface rfl PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals.row102Natural
end Row102

namespace Row110
private abbrev D := TwelvePointRemainingStructuralRow110Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow110Descriptor.schreierData
private def cubicWord : List (Fin 5) := [2,3,2]
private def cubic : Row110Top := (cubicWord.map (closureGenerators row110Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row110Interface :=
  C.jointDataAtTwo orbitCover row110Interface rfl PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals.row110Natural
end Row110

namespace Row111
private abbrev D := TwelvePointRemainingStructuralRow111Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow111Descriptor.schreierData
private def cubicWord : List (Fin 5) := [3,3]
private def cubic : Row111Top := (cubicWord.map (closureGenerators row111Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row111Interface :=
  C.jointDataAtTwo orbitCover row111Interface rfl PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals.row111Natural
end Row111

namespace Row114
private abbrev D := TwelvePointRemainingStructuralRow114Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow114Descriptor.schreierData
private def cubicWord : List (Fin 5) := [4,2,2,4]
private def cubic : Row114Top := (cubicWord.map (closureGenerators row114Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row114Interface :=
  C.jointDataAtTwo orbitCover row114Interface rfl PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals.row114Natural
end Row114

namespace Row115
private abbrev D := TwelvePointRemainingStructuralRow115Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow115Descriptor.schreierData
private def cubicWord : List (Fin 4) := [3,2,2,3]
private def cubic : Row115Top := (cubicWord.map (closureGenerators row115Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row115Interface :=
  C.jointDataAtTwo orbitCover row115Interface rfl PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals.row115Natural
end Row115

namespace Row146
private abbrev D := TwelvePointRemainingStructuralRow146Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow146Descriptor.schreierData
private def cubicWord : List (Fin 5) := [2,3,2]
private def cubic : Row146Top := (cubicWord.map (closureGenerators row146Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row146Interface :=
  C.jointDataAtTwo orbitCover row146Interface rfl PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals.row146Natural
end Row146

namespace Row149
private abbrev D := TwelvePointRemainingStructuralRow149Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow149Descriptor.schreierData
private def cubicWord : List (Fin 5) := [4,2,4]
private def cubic : Row149Top := (cubicWord.map (closureGenerators row149Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row149Interface :=
  C.jointDataAtTwo orbitCover row149Interface rfl PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals.row149Natural
end Row149

namespace Row184
private abbrev D := TwelvePointRemainingStructuralRow184Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow184Descriptor.schreierData
private def cubicWord : List (Fin 4) := [1,2,1]
private def cubic : Row184Top := (cubicWord.map (closureGenerators row184Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row184Interface :=
  C.jointDataAtTwo orbitCover row184Interface rfl DegreeTwoTwelveThreeBlockNaturalFamily.row184Natural
end Row184

namespace Row190
private abbrev D := TwelvePointRemainingStructuralRow190Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow190Descriptor.schreierData
private def cubicWord : List (Fin 4) := [1,2,1]
private def cubic : Row190Top := (cubicWord.map (closureGenerators row190Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row190Interface :=
  C.jointDataAtTwo orbitCover row190Interface rfl DegreeTwoTwelveThreeBlockNaturalFamily.row190Natural
end Row190

namespace Row191
private abbrev D := TwelvePointRemainingStructuralRow191Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow191Descriptor.schreierData
private def cubicWord : List (Fin 4) := [1,2,1]
private def cubic : Row191Top := (cubicWord.map (closureGenerators row191Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row191Interface :=
  C.jointDataAtTwo orbitCover row191Interface rfl DegreeTwoTwelveThreeBlockNaturalFamily.row191Natural
end Row191

namespace Row227
private abbrev D := TwelvePointRemainingStructuralRow227Descriptor.generatorData
private abbrev C := TwelvePointRemainingStructuralRow227Descriptor.schreierData
private def cubicWord : List (Fin 4) := [1,2,1]
private def cubic : Row227Top := (cubicWord.map (closureGenerators row227Generators)).prod
private def representative : Fin 2 → Fin 6 := ![0,2]
private def orbitIndex : Fin 6 → Fin 2 := ![0,0,1,1,1,0]
private def exponent : Fin 6 → ℕ := ![0,2,0,2,1,1]

def orbitCover : SymmetricPairTwoOrbitCover D where
  cubic := cubic
  representative := representative
  cover := by
    intro x
    refine ⟨orbitIndex x,exponent x,?_⟩
    have ht : D.frame.top cubic=D.topEmbedding ((cubicWord.map D.codes).prod) :=
      word_top D cubicWord
    rw [ht]
    exact (by decide +kernel : ∀ y : Fin 6,
      (D.topEmbedding ((cubicWord.map D.codes).prod) ^ exponent y)
        (representative (orbitIndex y))=y) x

def dataAtTwo : DegreeTwoTwelveFlexibleProfiles.Data row227Interface :=
  C.jointDataAtTwo orbitCover row227Interface rfl PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily.row227Natural
end Row227

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSignedS4JointClients
