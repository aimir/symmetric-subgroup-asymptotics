import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePresentationWords
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu12.Cardinality
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Coset.Card

/-! A genuine representation of the exact pinned M12 presentation in the
original12-point generated subgroup. Inherited pinned simplicity and a
nonidentity image imply injectivity and order divisibility by95040.
No surjectivity or identification of the two group models is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualRepresentation
open CFSGMathieuTwelvePresentationWords

def representation : CFSG.Models.Presentations.M12.Model →* CFSG.Certificates.Mathieu12.M12 :=
  PresentedGroup.toGroup all_relators

theorem representation_of_zero : representation (PresentedGroup.of (0 : Fin 2)) = x := by
  simp [representation, generators]

theorem representation_of_one : representation (PresentedGroup.of (1 : Fin 2)) = y := by
  simp [representation, generators]

theorem representation_injective [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    Function.Injective representation := by
  rcases (inferInstance : representation.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact representation.ker_eq_bot_iff.mp hbot
  · have hm : PresentedGroup.of (1 : Fin 2) ∈ representation.ker := by rw [htop]; trivial
    have he : representation (PresentedGroup.of (1 : Fin 2)) = 1 := hm
    exact (y_ne_one (representation_of_one.symm.trans he)).elim

theorem card_dvd [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    Nat.card CFSG.Models.Presentations.M12.Model ∣ 95040 := by
  have hd := Subgroup.card_dvd_of_injective representation representation_injective
  rw [CFSG.Certificates.Mathieu12.M12Cardinality.card_M12] at hd
  exact hd

def permutationRepresentation : CFSG.Models.Presentations.M12.Model →* Equiv.Perm (Fin 12) :=
  CFSG.Certificates.Mathieu12.M12Subgroup.subtype.comp representation

theorem permutationRepresentation_injective [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    Function.Injective permutationRepresentation :=
  CFSG.Certificates.Mathieu12.M12Subgroup.subtype_injective.comp representation_injective

theorem permutationRepresentation_of_zero :
    permutationRepresentation (PresentedGroup.of (0 : Fin 2)) = xPermutation := by
  change (representation (PresentedGroup.of (0 : Fin 2))).val = xPermutation
  rw [representation_of_zero, x_coe_eq]

theorem permutationRepresentation_of_one :
    permutationRepresentation (PresentedGroup.of (1 : Fin 2)) = yPermutation := by
  change (representation (PresentedGroup.of (1 : Fin 2))).val = yPermutation
  rw [representation_of_one, y_coe_eq]

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualRepresentation
