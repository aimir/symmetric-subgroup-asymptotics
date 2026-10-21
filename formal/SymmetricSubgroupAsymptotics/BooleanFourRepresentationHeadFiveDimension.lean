import SymmetricSubgroupAsymptotics.BinaryBooleanFourRepresentationLeadingMiddle
import SymmetricSubgroupAsymptotics.BooleanFourFullPrefixThreeGenerators
import SymmetricSubgroupAsymptotics.RepresentationLeadingPrefixDimension
import SymmetricSubgroupAsymptotics.RepresentationDifferenceOperator

/-! A prefix bound for an abstract original representation. The actual
translation differences and full prefix stability retain all lower terms;
the dimension-thirteen endpoint has just three genuine generators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
variable {G M : Type} [Group G] [AddCommGroup M] [Module (ZMod 2) M]
    [FiniteDimensional (ZMod 2) M]

private theorem quadratic_label_lt_thirteen :
    ∀ a : Fin 16,(support a).card=2 → a.val<13 := by decide +kernel

theorem boolean_four_representation_head_five_dimension_le_twelve
    (rho : Representation (ZMod 2) G M) (C : M →ₗ[ZMod 2] V)
    (hC : Function.Injective C)
    (hdiff : ∀ i : Fin 4,∃ g : G,∀ v : M,C (rho g v-v)=derivative i (C v))
    (hstable : ∀ (g : G) (v : M),
      (∀ j : Fin 16,13≤j.val → C v j=0) →
      ∀ j : Fin 16,13≤j.val → C (rho g v) j=0)
    (hhead : 5≤Module.finrank (ZMod 2)
      (rho.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    Module.finrank (ZMod 2) M≤12 := by
  letI : Module (ZMod 2)[G] rho.asModule :=
    Representation.instModuleMonoidAlgebraAsModule rho
  obtain ⟨S,label,hspan,hlead,_⟩ :=
    boolean_four_representation_generators_quadratic_leading rho C hC
      hdiff hhead
  have hlead13 : ∀ v∈S,∃ a : Fin 16,a.val<13 ∧
      FiniteRowLeadingWeight.HasLeading (C (rho.asModuleEquiv v)) a := by
    intro v hv
    exact ⟨label v,quadratic_label_lt_thirteen _ (hlead v hv).2,(hlead v hv).1⟩
  have hvan := representation_leading_prefix_vanishes rho C S hspan hlead13 hstable
  have hdim := representation_finrank_le_of_leading_prefix rho C hC (by decide : 13≤16)
    S hspan hlead13 hstable
  by_contra hn
  have heq : Module.finrank (ZMod 2) M=13 := by omega
  let E := C.comp rho.asModuleEquiv.toLinearMap
  have hE : Function.Injective E := hC.comp rho.asModuleEquiv.injective
  have hrange : E.range=prefixChart.space := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v,rfl⟩
      exact (mem_prefixChart _).mpr (hvan (rho.asModuleEquiv v))
    · rw [LinearMap.finrank_range_of_inj hE,rho.asModuleEquiv.finrank_eq,heq,prefixChart.finrank]
  have hd (i : Fin 4) (v : rho.asModule) :
      ∃ r : (ZMod 2)[G],E (r • v)=derivative i (E v) := by
    refine ⟨MonoidAlgebra.single (hdiff i).choose (1 : ZMod 2)-1,?_⟩
    change C (rho.asModuleEquiv ((MonoidAlgebra.single (hdiff i).choose (1 : ZMod 2)-1) • v))=_
    rw [representation_difference_operator]
    exact (hdiff i).choose_spec (rho.asModuleEquiv v)
  obtain ⟨v,hv⟩ := boolean_four_full_prefix_generatedBy_three (A := (ZMod 2)[G]) E hE hrange hd
  have hh := representationHead_finrank_le_generators rho v hv
  omega

end SymmetricSubgroupAsymptotics
