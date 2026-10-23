import SymmetricSubgroupAsymptotics.CFSGFFourE6ProjectiveOrder

/-! Literal projection of the folded E6 matrix group onto the ORIGINAL
F4 projective model. The named positive Sylow survives both the SAME
action-image map and its central quotient injectively. No faithfulness
of the full folded source representation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalProjection
open CFSGFFourSerreMatrices CFSGFFourOriginalGoodSylow CFSGFFourE6ProjectiveOrder
open CFSGFFourE6PositiveSylow CFSGFFourE6PositiveActionInjective
open CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

local instance imageFinite (K : Type) [Field K] [Finite K] : Finite (imageGroup K) :=
  Finite.of_surjective (foldedToImage K) (foldedToImage_surjective K)

def imageToOriginal (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : imageGroup K→*Projective CartanMatrix.F₄ K :=
  (originalProjectiveEquiv K).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center (imageGroup K)))

theorem imageToOriginal_surjective (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : Function.Surjective (imageToOriginal K) :=
  (originalProjectiveEquiv K).symm.surjective.comp (QuotientGroup.mk'_surjective _)

theorem imageToOriginal_kernel (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (imageToOriginal K).ker=Subgroup.center (imageGroup K) :=
  (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (Subgroup.center (imageGroup K)))
    (originalProjectiveEquiv K).symm).trans (QuotientGroup.ker_mk' _)

def foldedToOriginal (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    canonicalElementaryGroup realizationData K→*Projective CartanMatrix.F₄ K :=
  (imageToOriginal K).comp (foldedToImage K)

theorem foldedToOriginal_surjective (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : Function.Surjective (foldedToOriginal K) :=
  (imageToOriginal_surjective K).comp (foldedToImage_surjective K)

def positiveToOriginal (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    imagePositiveSylow K p→*Projective CartanMatrix.F₄ K :=
  (imageToOriginal K).comp (imagePositiveSylow K p : Subgroup (imageGroup K)).subtype

theorem positiveToOriginal_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Function.Injective (positiveToOriginal K p) := by
  intro x y he
  apply CFSGDisjointSylowProjectiveOrder.quotient_center_sylow_injective
    (imagePositiveSylow K p) (imageNegativeSylow K p) (imageSylows_disjoint K p)
  exact (originalProjectiveEquiv K).symm.injective he

def positiveToImageSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : positiveSylow K p→*imagePositiveSylow K p :=
  (positiveRestriction K p).codRestrict (imagePositiveSylow K p : Subgroup (imageGroup K))
    (fun x=>⟨x.val,x.property,rfl⟩)

theorem positiveToImageSylow_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Function.Injective (positiveToImageSylow K p) := by
  intro x y he
  exact positiveRestriction_injective K p
    (congrArg (fun z : imagePositiveSylow K p=>z.val) he)

def foldedPositiveToOriginal (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    positiveSylow K p→*Projective CartanMatrix.F₄ K :=
  (positiveToOriginal K p).comp (positiveToImageSylow K p)

theorem foldedPositiveToOriginal_apply (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (x : positiveSylow K p) : foldedPositiveToOriginal K p x=foldedToOriginal K x.val := rfl

theorem foldedPositiveToOriginal_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Function.Injective (foldedPositiveToOriginal K p) :=
  (positiveToOriginal_injective K p).comp (positiveToImageSylow_injective K p)

def originalPositiveSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Sylow p (Projective CartanMatrix.F₄ K) :=
  (imagePositiveSylow K p).mapSurjective (f:=imageToOriginal K) (imageToOriginal_surjective K)

theorem original_finite (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : Finite (Projective CartanMatrix.F₄ K) :=
  Finite.of_surjective (imageToOriginal K) (imageToOriginal_surjective K)

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalProjection
