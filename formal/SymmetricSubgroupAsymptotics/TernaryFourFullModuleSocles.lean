import SymmetricSubgroupAsymptotics.TernaryFourFullModuleCoordinates
import SymmetricSubgroupAsymptotics.TernaryCentralComplementSocles
import SymmetricSubgroupAsymptotics.AffineIrreducibleQuotientSocles

/-! The full four-coordinate module inherits the actual central-complement
quotient bound. The faithful irreducible augmentation quotient and the
central prime factor transfer keep every original epimorphism unchanged. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryFourFullModuleSocles

open TernaryFourAugmentationRepresentation SemidirectProduct
open TernaryCentralComplementSocles

variable (R : Subgroup LinearGroup) (hR : evenHom.range ≤ R)

include hR in
theorem socle_of_surjective {t : ℕ} (ht : 1 ≤ t)
    (hproduct : ∀ N : Subgroup (R × C3), ∀ _ : N.Normal,
      SocleNormalGeneratorBound ((R × C3) ⧸ N) t)
    {X : Type} [Group X] (rho : AffineModel.Aff R × C3 →* X)
    (hrho : Function.Surjective rho) : SocleNormalGeneratorBound X t := by
  apply (TernaryFourAugmentationCentralCore.core R hR).product_socle_of_surjective C3
    (TernaryFourAugmentationCentralCore.core_ne_bot R hR)
    (rightHom : AffineModel.Aff R →* R) rightHom_surjective
    (by exact range_inl_eq_ker_rightHom.symm) ht _ hproduct rho hrho
  intro N hN
  letI := hN
  apply AffineModel.quotientSocle_of_irreducible_complement_quotients R
    (irreducible_of_even_range_le R hR) (Pi.single 0 1) _ ht _ N
  · intro he
    have hz := congrFun he 0
    norm_num at hz
  · intro M hM
    letI := hM
    let pi : R × C3 →* R ⧸ M := (QuotientGroup.mk' M).comp (MonoidHom.fst R C3)
    have hpi : Function.Surjective pi := (QuotientGroup.mk'_surjective M).comp Prod.fst_surjective
    exact CyclicSocleQuotientTools.socleBound_equiv
      (QuotientGroup.quotientKerEquivOfSurjective pi hpi) (hproduct pi.ker inferInstance)

theorem alternating_socle_of_surjective {X : Type} [Group X]
    (rho : AffineModel.Aff alternatingLinearGroup × C3 →* X)
    (hrho : Function.Surjective rho) : SocleNormalGeneratorBound X 2 := by
  apply socle_of_surjective alternatingLinearGroup le_rfl (by decide) _ rho hrho
  intro N hN
  letI := hN
  let e := evenHom.rangeRestrict.prodMap (MonoidHom.id C3)
  have he : Function.Surjective e := by
    intro x
    obtain ⟨g,hg⟩ := evenHom.rangeRestrict_surjective x.1
    exact ⟨(g,x.2),Prod.ext hg rfl⟩
  exact alternatingFour_product_socle_of_surjective ((QuotientGroup.mk' N).comp e)
    ((QuotientGroup.mk'_surjective N).comp he)

theorem symmetric_socle_of_surjective {X : Type} [Group X]
    (rho : AffineModel.Aff symmetricLinearGroup × C3 →* X)
    (hrho : Function.Surjective rho) : SocleNormalGeneratorBound X 1 := by
  have hR : evenHom.range ≤ symmetricLinearGroup := by
    rintro _ ⟨g,rfl⟩
    exact ⟨g.1,rfl⟩
  apply socle_of_surjective symmetricLinearGroup hR (by decide) _ rho hrho
  intro N hN
  letI := hN
  let e := hom.rangeRestrict.prodMap (MonoidHom.id C3)
  have he : Function.Surjective e := by
    intro x
    obtain ⟨g,hg⟩ := hom.rangeRestrict_surjective x.1
    exact ⟨(g,x.2),Prod.ext hg rfl⟩
  exact symmetricFour_product_socle_of_surjective ((QuotientGroup.mk' N).comp e)
    ((QuotientGroup.mk'_surjective N).comp he)

end SymmetricSubgroupAsymptotics.TernaryFourFullModuleSocles

end
