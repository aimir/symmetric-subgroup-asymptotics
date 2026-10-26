import SymmetricSubgroupAsymptotics.CFSGMathieuElevenPresentationWords
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu11.Cardinality
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Coset.Card

/-! The exact pinned M11 presentation has a genuine representation in
the original11-point generated subgroup. Inherited simplicity of the
PINNED presentation and one nontrivial literal image give injectivity.
This proves order divisibility by7920, without identifying the models or
assuming surjectivity, full order, or simplicity of the original model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualRepresentation
open CFSGMathieuElevenPresentationWords

def representation : CFSG.Models.Presentations.M11.Model →* CFSG.Certificates.Mathieu11.M11 :=
  PresentedGroup.toGroup all_relators

theorem representation_of_zero : representation (PresentedGroup.of (0 : Fin 2))=x := by
  simp [representation,generators]

theorem representation_of_one : representation (PresentedGroup.of (1 : Fin 2))=y := by
  simp [representation,generators]

theorem representation_injective [IsSimpleGroup CFSG.Models.Presentations.M11.Model] :
    Function.Injective representation := by
  rcases (inferInstance : representation.ker.Normal).eq_bot_or_eq_top with hbot|htop
  · exact representation.ker_eq_bot_iff.mp hbot
  · have hm : PresentedGroup.of (1 : Fin 2)∈representation.ker := by rw [htop]; trivial
    have he : representation (PresentedGroup.of (1 : Fin 2))=1 := hm
    exact (y_ne_one (representation_of_one.symm.trans he)).elim

theorem card_dvd [IsSimpleGroup CFSG.Models.Presentations.M11.Model] :
    Nat.card CFSG.Models.Presentations.M11.Model∣7920 := by
  have hd := Subgroup.card_dvd_of_injective representation representation_injective
  rw [CFSG.Certificates.Mathieu11.M11Cardinality.card_M11] at hd
  exact hd

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualRepresentation
