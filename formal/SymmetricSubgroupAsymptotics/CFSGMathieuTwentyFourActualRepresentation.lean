import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourPresentationWords
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Finite.Perm

/-! The exact pinned M24 presentation has a genuine injective representation
in the original24-point subgroup under inherited pinned simplicity.
This gives source-cardinality divisibility by24!, without using the heavy
actual-order certificates, any recovery word, or a model-identification
assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourActualRepresentation
open CFSGMathieuTwentyFourPresentationWords

def representation : CFSG.Models.Presentations.M24.Model →* CFSG.Certificates.Mathieu24.M24 :=
  PresentedGroup.toGroup all_relators

theorem representation_of_zero : representation (PresentedGroup.of (0 : Fin 2)) = x := by
  simp [representation, generators]

theorem representation_of_one : representation (PresentedGroup.of (1 : Fin 2)) = y := by
  simp [representation, generators]

theorem representation_injective [IsSimpleGroup CFSG.Models.Presentations.M24.Model] :
    Function.Injective representation := by
  rcases (inferInstance : representation.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact representation.ker_eq_bot_iff.mp hbot
  · have hm : PresentedGroup.of (1 : Fin 2) ∈ representation.ker := by rw [htop]; trivial
    have he : representation (PresentedGroup.of (1 : Fin 2)) = 1 := hm
    exact (y_ne_one (representation_of_one.symm.trans he)).elim

def permutationRepresentation : CFSG.Models.Presentations.M24.Model →* Equiv.Perm (Fin 24) :=
  CFSG.Certificates.Mathieu24.M24Subgroup.subtype.comp representation

theorem permutationRepresentation_injective [IsSimpleGroup CFSG.Models.Presentations.M24.Model] :
    Function.Injective permutationRepresentation :=
  CFSG.Certificates.Mathieu24.M24Subgroup.subtype_injective.comp representation_injective

theorem permutationRepresentation_of_zero :
    permutationRepresentation (PresentedGroup.of (0 : Fin 2)) = xPermutation := by
  change (representation (PresentedGroup.of (0 : Fin 2))).val = xPermutation
  rw [representation_of_zero, x_coe_eq]

theorem permutationRepresentation_of_one :
    permutationRepresentation (PresentedGroup.of (1 : Fin 2)) = yPermutation := by
  change (representation (PresentedGroup.of (1 : Fin 2))).val = yPermutation
  rw [representation_of_one, y_coe_eq]

theorem card_dvd_factorial [IsSimpleGroup CFSG.Models.Presentations.M24.Model] :
    Nat.card CFSG.Models.Presentations.M24.Model ∣ Nat.factorial 24 := by
  simpa only [Nat.card_perm, Nat.card_fin] using
    Subgroup.card_dvd_of_injective permutationRepresentation permutationRepresentation_injective

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourActualRepresentation
