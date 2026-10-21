import SymmetricSubgroupAsymptotics.BooleanFourLeadingGeneratorsMiddle
import SymmetricSubgroupAsymptotics.BinaryBooleanFourDerivativeWords
import SymmetricSubgroupAsymptotics.RepresentationGeneratorHead
import SymmetricSubgroupAsymptotics.FiniteModulePaddedGenerators

/-! Quadratic leading generators in an original representation whose
actual translation differences are the four Boolean derivatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

variable {G V₀ : Type} [Group G] [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [FiniteDimensional (ZMod 2) V₀]

theorem boolean_four_representation_generators_quadratic_leading
    (rho : Representation (ZMod 2) G V₀) (C : V₀ →ₗ[ZMod 2] V)
    (hC : Function.Injective C)
    (hderivative : ∀ i : Fin 4, ∃ g : G, ∀ v : V₀,
      C (rho g v - v) = derivative i (C v))
    (hhead : 5 ≤ Module.finrank (ZMod 2)
      (rho.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    ∃ (S : Finset rho.asModule) (label : rho.asModule → Fin 16),
      Submodule.span (ZMod 2)[G] (S : Set rho.asModule) = ⊤ ∧
      (∀ v ∈ S, FiniteRowLeadingWeight.HasLeading (C (rho.asModuleEquiv v)) (label v) ∧
        (support (label v)).card = 2) ∧
      Set.InjOn label (S : Set rho.asModule) := by
  let E : rho.asModule →ₗ[ZMod 2] V := C.comp rho.asModuleEquiv.toLinearMap
  have hE : Function.Injective E := hC.comp rho.asModuleEquiv.injective
  have hd : ModuleGeneratedBy (ZMod 2)[G] rho.asModule (Module.finrank (ZMod 2) V₀) :=
    representationGeneratedBy_scalar_finrank rho
  have hdiff : ∀ i : Fin 4, ∀ v : rho.asModule,
      ∃ r : (ZMod 2)[G], E (r • v) = derivative i (E v) := by
    intro i v
    obtain ⟨g, hg⟩ := hderivative i
    refine ⟨MonoidAlgebra.single g (1 : ZMod 2) - 1, ?_⟩
    rw [sub_smul, Representation.single_smul, one_smul, one_smul]
    exact hg (rho.asModuleEquiv v)
  apply boolean_four_generating_finset_with_quadratic_leading_terms hd E hE
  · intro v a b hv hab
    exact exists_operator_leading_subset E hdiff v a b hv hab
  · intro S hS
    obtain ⟨v, hv⟩ := ModuleGeneratedBy.of_finset_card_le S hS S.card le_rfl
    exact hhead.trans (representationHead_finrank_le_generators rho v hv)

end SymmetricSubgroupAsymptotics
