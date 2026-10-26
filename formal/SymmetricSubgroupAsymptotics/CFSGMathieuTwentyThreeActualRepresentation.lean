import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePresentationWords
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu23.Cardinality
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Coset.Card

/-! A genuine representation of the exact pinned M23 presentation in the
original23-point generated subgroup. Inherited pinned simplicity and a
nonidentity image imply injectivity and order divisibility by10200960.
No surjectivity or identification of the two group models is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeActualRepresentation
open CFSGMathieuTwentyThreePresentationWords

def representation : CFSG.Models.Presentations.M23.Model →* CFSG.Certificates.Mathieu23.M23 :=
  PresentedGroup.toGroup all_relators

theorem representation_of_zero : representation (PresentedGroup.of (0 : Fin 2)) = x := by
  simp [representation, generators]

theorem representation_of_one : representation (PresentedGroup.of (1 : Fin 2)) = y := by
  simp [representation, generators]

theorem representation_injective [IsSimpleGroup CFSG.Models.Presentations.M23.Model] :
    Function.Injective representation := by
  rcases (inferInstance : representation.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact representation.ker_eq_bot_iff.mp hbot
  · have hm : PresentedGroup.of (1 : Fin 2) ∈ representation.ker := by rw [htop]; trivial
    have he : representation (PresentedGroup.of (1 : Fin 2)) = 1 := hm
    exact (y_ne_one (representation_of_one.symm.trans he)).elim

theorem card_dvd [IsSimpleGroup CFSG.Models.Presentations.M23.Model] :
    Nat.card CFSG.Models.Presentations.M23.Model ∣ 10200960 := by
  have hd := Subgroup.card_dvd_of_injective representation representation_injective
  rw [CFSG.Certificates.Mathieu23.M23Cardinality.card_M23] at hd
  exact hd

def permutationRepresentation : CFSG.Models.Presentations.M23.Model →* Equiv.Perm (Fin 23) :=
  CFSG.Certificates.Mathieu23.M23Subgroup.subtype.comp representation

theorem permutationRepresentation_injective [IsSimpleGroup CFSG.Models.Presentations.M23.Model] :
    Function.Injective permutationRepresentation :=
  CFSG.Certificates.Mathieu23.M23Subgroup.subtype_injective.comp representation_injective

theorem permutationRepresentation_of_zero :
    permutationRepresentation (PresentedGroup.of (0 : Fin 2)) = xPermutation := by
  change (representation (PresentedGroup.of (0 : Fin 2))).val = xPermutation
  rw [representation_of_zero, x_coe_eq]

theorem permutationRepresentation_of_one :
    permutationRepresentation (PresentedGroup.of (1 : Fin 2)) = yPermutation := by
  change (representation (PresentedGroup.of (1 : Fin 2))).val = yPermutation
  rw [representation_of_one, y_coe_eq]

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeActualRepresentation
