import SymmetricSubgroupAsymptotics.BinaryRegular46HeadThreeMonomialData
import SymmetricSubgroupAsymptotics.BinaryCommonEightExtraShearLeading
import SymmetricSubgroupAsymptotics.AlgebraLeadingGeneratorAntichain
import SymmetricSubgroupAsymptotics.RepresentationGeneratorHead
import SymmetricSubgroupAsymptotics.FiniteModulePaddedGenerators

/-! A head-three original representation retains at least three actual
kernel generators whose leading labels are incomparable under genuine
translations and the additional original top shear. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
open BinaryRegular46HeadThreeMonomial
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

variable {G V₀ : Type} [Group G] [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [FiniteDimensional (ZMod 2) V₀]

theorem binary_head_three_actual_leading_antichain
    (rho : Representation (ZMod 2) G V₀) (C : V₀ →ₗ[ZMod 2] V)
    (hC : Function.Injective C)
    (hderivative : ∀ i : Fin 4, ∃ g : G, ∀ v : V₀,
      C (rho g v - v) = derivative i (C v))
    (hextra : ∃ g : G, ∀ v : V₀,
      C (rho g v - v) = BinaryCommonEightExtraShearLeading.operator (C v))
    (hhead : 3 ≤ Module.finrank (ZMod 2)
      (rho.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    ∃ (S : Finset rho.asModule) (label : rho.asModule → Fin 16),
      Submodule.span (ZMod 2)[G] (S : Set rho.asModule) = ⊤ ∧
      (∀ v ∈ S, FiniteRowLeadingWeight.HasLeading (C (rho.asModuleEquiv v)) (label v)) ∧
      Set.InjOn label (S : Set rho.asModule) ∧
      IsAntichain TopRel (S.image label : Set (Fin 16)) ∧
      3 ≤ (S.image label).card := by
  let E : rho.asModule →ₗ[ZMod 2] V := C.comp rho.asModuleEquiv.toLinearMap
  have hE : Function.Injective E := hC.comp rho.asModuleEquiv.injective
  have hd : ModuleGeneratedBy (ZMod 2)[G] rho.asModule (Module.finrank (ZMod 2) V₀) :=
    representationGeneratedBy_scalar_finrank rho
  have hstep : ∀ op a b, topStep op a = some b → ∀ v : rho.asModule,
      FiniteRowLeadingWeight.HasLeading (E v) a →
      ∃ r : (ZMod 2)[G], FiniteRowLeadingWeight.HasLeading (E (r • v)) b := by
    intro op a b hab v hv
    cases op with
    | derivative i =>
      change (if i ∈ support a then some (removeIndex i a) else none) = some b at hab
      split_ifs at hab with hi
      have he : removeIndex i a = b := Option.some.inj hab
      subst b
      obtain ⟨g, hg⟩ := hderivative i
      refine ⟨MonoidAlgebra.single g (1 : ZMod 2) - 1, ?_⟩
      rw [sub_smul, Representation.single_smul, one_smul, one_smul]
      change FiniteRowLeadingWeight.HasLeading (C (rho g (rho.asModuleEquiv v) -
        rho.asModuleEquiv v)) _
      rw [hg]
      exact derivative_hasLeading i a (E v) hv hi
    | extra =>
      change (if h : a.val % 2 = 1 ∧ a.val < 8 then
        some ⟨a.val + 7, by omega⟩ else none) = some b at hab
      split_ifs at hab with h
      have he : (⟨a.val + 7, by omega⟩ : Fin 16) = b := Option.some.inj hab
      subst b
      obtain ⟨g, hg⟩ := hextra
      refine ⟨MonoidAlgebra.single g (1 : ZMod 2) - 1, ?_⟩
      rw [sub_smul, Representation.single_smul, one_smul, one_smul]
      change FiniteRowLeadingWeight.HasLeading (C (rho g (rho.asModuleEquiv v) -
        rho.asModuleEquiv v)) _
      rw [hg]
      have ht : BinaryCommonEightExtraShearLeading.target a =
          (⟨a.val + 7, by omega⟩ : Fin 16) := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by omega)
      rw [← ht]
      exact BinaryCommonEightExtraShearLeading.operator_hasLeading (E v) a hv h.1 h.2
    | shear k => simp only [topStep, reduceCtorEq] at hab
  have hrefl : ∀ a : Fin 16, TopRel a a := by decide
  obtain ⟨S, label, hspan, hlead, hinj, hanti⟩ :=
    algebra_generating_finset_with_leading_antichain hd E hE 0 TopRel hrefl (by
      intro v a b hv hab
      exact ModuleLeadingOperatorWords.exists_operator_of_run topStep
        (fun v a => FiniteRowLeadingWeight.HasLeading (E v) a)
        hstep _ a b (topPaths_valid a b hab) v hv)
  refine ⟨S, label, hspan, (fun v hv => (hlead v hv).2), hinj, hanti, ?_⟩
  have hs : 3 ≤ S.card := by
    obtain ⟨v, hv⟩ := ModuleGeneratedBy.of_finset_card_le S hspan S.card le_rfl
    exact hhead.trans (representationHead_finrank_le_generators rho v hv)
  rwa [Finset.card_image_of_injOn hinj]

end SymmetricSubgroupAsymptotics
