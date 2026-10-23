import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveImageSylow
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOppositeActionIntersection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedProjectiveImage
import SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveCardinality

/-! A q^24 order lower bound in the SAME ORIGINAL simple triality model.
The literal ORIGINAL fixed opposition normalizes the Derived action range;
it need not itself lie in Derived. Two actual disjoint Sylows survive the
central quotient by the proved central-p-element separation lemma. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOrderLower
open CFSGTrialityGeckFixedPositiveImageSylow CFSGTrialityGeckDerivedSylowNormalizer
open CFSGTrialityGeckLongDerivedImage CFSGTrialityGeckSourceWordAction
open CFSGTrialityGeckOriginalFixedSections
open CFSGTrialityGeckSourceRelativeWords CFSGTrialityGeckRelativeOpposition
open CFSGTrialityGeckOppositeActionIntersection CFSGTrialityGeckDerivedProjectiveImage
open CFSGTrialityTripleFixedRoots

local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) : Finite (DerivedImage q) :=
  Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)

private def restrictConjugation {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hf : ∀ x ∈ H,g*x*g⁻¹ ∈ H) (hb : ∀ x ∈ H,g⁻¹*x*g ∈ H) : MulAut H where
  toFun x := ⟨g*x.val*g⁻¹,hf x.val x.property⟩
  invFun x := ⟨g⁻¹*x.val*g,hb x.val x.property⟩
  left_inv x := by apply Subtype.ext; change g⁻¹*(g*x.val*g⁻¹)*g=x.val; group
  right_inv x := by apply Subtype.ext; change g*(g⁻¹*x.val*g)*g⁻¹=x.val; group
  map_mul' x y := by apply Subtype.ext; change g*(x.val*y.val)*g⁻¹=(g*x.val*g⁻¹)*(g*y.val*g⁻¹); group

private theorem source_conjugates_image (q : CFSG.PrimePower) (s : Fixed q)
    (a : DerivedImage q) :
    fixedImageAction q s*a.val*(fixedImageAction q s)⁻¹ ∈ DerivedImage q := by
  obtain ⟨d,hd⟩ := a.property
  have hm := conjugate_image_mem q s d.val (show fixedImageAction q d.val ∈ DerivedImage q from ⟨d,rfl⟩)
  have hd' : fixedImageAction q d.val = a.val := hd
  rw [map_mul,map_mul,map_inv,hd'] at hm
  exact hm

def sourceConjugation (q : CFSG.PrimePower) (s : Fixed q) : MulAut (DerivedImage q) :=
  restrictConjugation (DerivedImage q) (fixedImageAction q s)
    (fun x hx => source_conjugates_image q s ⟨x,hx⟩) (fun x hx => by
      simpa only [map_inv,inv_inv] using source_conjugates_image q s⁻¹ ⟨x,hx⟩)

def oppositionAut (q : CFSG.PrimePower) : MulAut (DerivedImage q) :=
  sourceConjugation q (sourceRelativeWord q oppositionRelativeWord)

theorem oppositionAut_apply (q : CFSG.PrimePower) (a : DerivedImage q) :
    (oppositionAut q a).val =
      matrixAction (q.Extension 3) (matrixWord (q.Extension 3) oppositionWord)*a.val*
        (matrixAction (q.Extension 3) (matrixWord (q.Extension 3) oppositionWord))⁻¹ := by
  change fixedImageAction q (sourceRelativeWord q oppositionRelativeWord)*a.val*
    (fixedImageAction q (sourceRelativeWord q oppositionRelativeWord))⁻¹ = _
  rw [sourceRelativeWord_action]
  rfl

def oppositeSylow (q : CFSG.PrimePower) : Sylow q.prime (DerivedImage q) :=
  (imagePositiveSylow q).mapSurjective (f := (oppositionAut q).toMonoidHom)
    (oppositionAut q).surjective

theorem oppositeSylow_card (q : CFSG.PrimePower) : Nat.card (oppositeSylow q) = q.order^12 := by
  have he := Nat.card_congr ((oppositionAut q).subgroupMap
    (imagePositiveSylow q : Subgroup (DerivedImage q))).toEquiv
  change Nat.card (imagePositiveSylow q) = Nat.card (oppositeSylow q) at he
  exact he.symm.trans (imagePositiveSylow_card q)

theorem oppositeSylows_disjoint (q : CFSG.PrimePower) :
    (imagePositiveSylow q : Subgroup (DerivedImage q)) ⊓
      (oppositeSylow q : Subgroup (DerivedImage q)) = ⊥ := by
  apply bot_unique
  intro a ha
  change a ∈ (imagePositiveSylow q : Subgroup (DerivedImage q)) ∧
    a ∈ (imagePositiveSylow q : Subgroup (DerivedImage q)).map (oppositionAut q).toMonoidHom at ha
  obtain ⟨b,hb,hba⟩ := ha.2
  obtain ⟨u,hu⟩ := exists_positive_lift q ⟨a,ha.1⟩
  obtain ⟨v,hv⟩ := exists_positive_lift q ⟨b,hb⟩
  have he : positiveAction (q.Extension 3) u.val =
      matrixAction (q.Extension 3) (matrixWord (q.Extension 3) oppositionWord)*
        positiveAction (q.Extension 3) v.val*
        (matrixAction (q.Extension 3) (matrixWord (q.Extension 3) oppositionWord))⁻¹ := by
    calc
      _ = a.val := hu
      _ = (oppositionAut q b).val := congrArg (fun x : DerivedImage q => x.val) hba.symm
      _ = _ := by rw [oppositionAut_apply,←hv]
  have hu1 := positive_opposite_action_eq_imp_one (q.Extension 3) q.prime u.val v.val he
  have ha1 : a.val = 1 := by rw [←hu,hu1,map_one]
  exact Subgroup.mem_bot.mpr (Subtype.ext ha1)

theorem original_card_lower (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : q.order^24 ≤ Nat.card (CFSG.Models.TrialityD4 q) := by
  have h := CFSGDisjointSylowProjectiveCardinality.card_mul_le_central_quotient
    (imagePositiveSylow q) (oppositeSylow q) (oppositeSylows_disjoint q)
  rw [imagePositiveSylow_card,oppositeSylow_card,←pow_add] at h
  rw [Nat.card_congr (originalProjectiveImageEquiv q).toEquiv]
  exact h

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOrderLower
