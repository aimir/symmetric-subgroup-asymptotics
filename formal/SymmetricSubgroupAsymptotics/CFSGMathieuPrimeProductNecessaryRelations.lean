import SymmetricSubgroupAsymptotics.FixedProductRelatorTransport
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeGoodSylowTwentyThree
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourGoodSylowTwentyThree
import SymmetricSubgroupAsymptotics.OuterFixedElementEvaluationBound

/-! All nine M23 and all seven M24 pinned relators are necessary for the
literal represented image h of pinnedX under an automorphism fixing the
product A=pinnedX*pinnedY. The second represented image is h^-1*A.
No simplicity, finite capacity, original-model recovery, or converse of
the relator conditions is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeProductNecessaryRelations
open CFSG.Models.Presentations.M23 CFSGMathieuTwentyThreeActualRepresentation
open CFSGMathieuTwentyThreeGoodSylowTwentyThree OuterFixedElementEvaluationBound
open FixedProductRelatorTransport

def fixedProduct : Equiv.Perm (Fin 23) := permutationRepresentation (pinnedX*pinnedY)

def Accepts (h : Equiv.Perm (Fin 23)) : Prop :=
  ∀ r ∈ relators, FreeGroup.lift (pair h (h⁻¹*fixedProduct)) r = 1

theorem pinned_relator (r : FreeGroup (Fin 2)) (hr : r ∈ relators) :
    FreeGroup.lift (pair pinnedX pinnedY) r = 1 :=
  presented_relator {w | w ∈ relators} r hr

theorem accepts_of_fixed_product (f : fixedAutomorphisms (pinnedX*pinnedY)) :
    Accepts (permutationRepresentation (f.val pinnedX)) := by
  let phi : Model →* Equiv.Perm (Fin 23) := permutationRepresentation.comp f.val.toMonoidHom
  have hproduct : phi (pinnedX*pinnedY) = fixedProduct := by
    change permutationRepresentation (f.val (pinnedX*pinnedY)) = fixedProduct
    rw [f.property]
    rfl
  intro r hr
  exact relator_transport phi pinnedX pinnedY fixedProduct hproduct r (pinned_relator r hr)

theorem accepts_at (h : Equiv.Perm (Fin 23)) (hh : Accepts h)
    (r : Fin relators.length) :
    FreeGroup.lift (pair h (h⁻¹*fixedProduct)) (relators.get r) = 1 :=
  hh _ (List.get_mem _ _)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeProductNecessaryRelations

namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourProductNecessaryRelations
open CFSG.Models.Presentations.M24 CFSGMathieuTwentyFourActualRepresentation
open CFSGMathieuTwentyFourGoodSylowTwentyThree OuterFixedElementEvaluationBound
open FixedProductRelatorTransport

def fixedProduct : Equiv.Perm (Fin 24) := permutationRepresentation (pinnedX*pinnedY)

def Accepts (h : Equiv.Perm (Fin 24)) : Prop :=
  ∀ r ∈ relators, FreeGroup.lift (pair h (h⁻¹*fixedProduct)) r = 1

theorem pinned_relator (r : FreeGroup (Fin 2)) (hr : r ∈ relators) :
    FreeGroup.lift (pair pinnedX pinnedY) r = 1 :=
  presented_relator {w | w ∈ relators} r hr

theorem accepts_of_fixed_product (f : fixedAutomorphisms (pinnedX*pinnedY)) :
    Accepts (permutationRepresentation (f.val pinnedX)) := by
  let phi : Model →* Equiv.Perm (Fin 24) := permutationRepresentation.comp f.val.toMonoidHom
  have hproduct : phi (pinnedX*pinnedY) = fixedProduct := by
    change permutationRepresentation (f.val (pinnedX*pinnedY)) = fixedProduct
    rw [f.property]
    rfl
  intro r hr
  exact relator_transport phi pinnedX pinnedY fixedProduct hproduct r (pinned_relator r hr)

theorem accepts_at (h : Equiv.Perm (Fin 24)) (hh : Accepts h)
    (r : Fin relators.length) :
    FreeGroup.lift (pair h (h⁻¹*fixedProduct)) (relators.get r) = 1 :=
  hh _ (List.get_mem _ _)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourProductNecessaryRelations
