import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveActionInjective
import SymmetricSubgroupAsymptotics.CFSGFFourE6OppositeActionImages
import SymmetricSubgroupAsymptotics.CFSGFFourE6OppositeSylow
import SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleParameters
import SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveOrderStrict

/-! A strict double-Sylow order bound for the ORIGINAL F4 projective
model. Only its actual projective simplicity is used in descent. The
positive Sylow cardinal survives the proved injective restriction; the
two image Sylows are genuinely disjoint before quotienting the centre.
No ambient E6 simplicity or faithfulness of the full F4 action is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6ProjectiveOrder
open CFSGFFourSerreMatrices CFSGFFourOriginalGoodSylow CFSGFFourE6PositiveSylow
open CFSGFFourE6PositiveActionInjective CFSGFFourE6OppositeSylow
open CFSGFFourE6OppositeActionImages CFSGFFourE6SimpleParameters
open CFSGFFourE6RootSubgroups CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

local instance imageFinite (K : Type) [Field K] [Finite K] : Finite (imageGroup K) :=
  Finite.of_surjective (foldedToImage K) (foldedToImage_surjective K)

def imageNegativeSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Sylow p (imageGroup K) :=
  (negativeSylow K p).mapSurjective (f:=foldedToImage K) (foldedToImage_surjective K)

theorem imageSylows_disjoint (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (imagePositiveSylow K p : Subgroup (imageGroup K)) ⊓
      (imageNegativeSylow K p : Subgroup (imageGroup K))=⊥ := by
  change (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)).map
      (foldedToImage K) ⊓
    (negativeSylow K p : Subgroup (canonicalElementaryGroup realizationData K)).map
      (foldedToImage K)=⊥
  rw [positiveSylow_coe,negativeSylow_coe]
  exact opposite_action_images_disjoint K

private def positiveSylowChart (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a : Fin 4 → K) : positiveSylow K p :=
  ⟨⟨foldedWord K a,foldedRootGroup_le_model K false (foldedWord_mem K a)⟩,
    (le_of_eq (positiveSylow_coe K p).symm)
      (foldedRootGroup_le_ambient K false (foldedWord_mem K a))⟩

theorem positiveSylow_card_gt_one (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : 1 < Nat.card (positiveSylow K p) := by
  have hinj : Function.Injective (positiveSylowChart K p) := by
    intro a b he
    apply foldedWord_injective K
    exact congrArg (fun z : positiveSylow K p=>z.val.val) he
  exact lt_of_lt_of_le (Finite.one_lt_card (α:=Fin 4 → K))
    (Nat.card_le_card_of_injective (positiveSylowChart K p) hinj)

def originalProjectiveEquiv (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Projective CartanMatrix.F₄ K ≃* imageGroup K ⧸ Subgroup.center (imageGroup K) := by
  let H := imageGroup K
  let pi := QuotientGroup.mk' (Subgroup.center H)
  have hne : pi (imageWeyl K)≠1 := by
    intro h
    exact imageWeyl_not_center K ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (H⧸Subgroup.center H) := ⟨⟨pi (imageWeyl K),1,hne⟩⟩
  exact CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (imageRepresentation realizationData K).rangeRestrict
    (imageRepresentation realizationData K).rangeRestrict_surjective

theorem serreTypeFFour_positive_square_lt_order (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Nat.card (positiveSylow K p)^2 < Nat.card (Projective CartanMatrix.F₄ K) := by
  have hP : 1 < Nat.card (imagePositiveSylow K p) := by
    rw [imagePositiveSylow_card]
    exact positiveSylow_card_gt_one K p
  have h := CFSGDisjointSylowProjectiveOrder.quotient_center_card_strict_lower
    (imagePositiveSylow K p) (imageNegativeSylow K p) (imageSylows_disjoint K p) hP
  rw [imagePositiveSylow_card] at h
  rw [Nat.card_congr (originalProjectiveEquiv K).toEquiv]
  exact h

end SymmetricSubgroupAsymptotics.CFSGFFourE6ProjectiveOrder
