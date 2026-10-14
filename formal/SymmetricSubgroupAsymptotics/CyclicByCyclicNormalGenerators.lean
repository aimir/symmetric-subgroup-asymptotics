import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineSocleGenerators
import Mathlib.GroupTheory.SemidirectProduct

/-! Every ambient normal subgroup of a finite cyclic-by-cyclic group has
at most two normal generators. The proof uses the actual kernel and image,
so it also applies to a nontrivial action on the cyclic kernel. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace CyclicByCyclicNormalGenerators

theorem normalGen_le_two {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] [IsCyclic E] [IsCyclic (G ⧸ E)]
    (H : Subgroup G) [H.Normal] : MarkedC4.normalGen H ≤ 2 := by
  letI : IsCyclic (H ⊓ E : Subgroup G) :=
    isCyclic_of_injective (Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective inf_le_right)
  letI : (H.map (QuotientGroup.mk' E)).Normal :=
    (inferInstance : H.Normal).map _ (QuotientGroup.mk'_surjective E)
  exact (MarkedC4.normalGen_normal_le_inter_add_image H E).trans
    (Nat.add_le_add
      (CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic (H ⊓ E))
      (CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic
        (H.map (QuotientGroup.mk' E))))

theorem semidirect_normalGen_le_two
    {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    [IsCyclic A] [IsCyclic B] (phi : B →* MulAut A)
    (H : Subgroup (A ⋊[phi] B)) [H.Normal] : MarkedC4.normalGen H ≤ 2 := by
  letI : Finite (A ⋊[phi] B) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  let E := (SemidirectProduct.rightHom : A ⋊[phi] B →* B).ker
  letI : IsCyclic E := by
    change IsCyclic (SemidirectProduct.rightHom : A ⋊[phi] B →* B).ker
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    exact isCyclic_of_surjective
      (SemidirectProduct.inl : A →* A ⋊[phi] B).rangeRestrict
      (SemidirectProduct.inl : A →* A ⋊[phi] B).rangeRestrict_surjective
  let e : (A ⋊[phi] B) ⧸ E ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective
      SemidirectProduct.rightHom SemidirectProduct.rightHom_surjective
  letI : IsCyclic ((A ⋊[phi] B) ⧸ E) :=
    isCyclic_of_injective e.toMonoidHom e.injective
  exact normalGen_le_two E H

end CyclicByCyclicNormalGenerators
end SymmetricSubgroupAsymptotics

end
