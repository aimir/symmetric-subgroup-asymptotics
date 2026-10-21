import SymmetricSubgroupAsymptotics.BinaryTriangularMinimumSupportSingletons
import SymmetricSubgroupAsymptotics.AlgebraMinimumFourLeadingGenerators
import SymmetricSubgroupAsymptotics.PGroupCoinvariantGenerators

/-! An actual head-four triangular submodule has four original minimum
generators. Their supports form an antichain and their full original
operator noncancellation property is retained for the singleton case. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryTriangularPointCoordinates
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {G X : Type} [Group G] [MulAction G X] [Finite X]
    (T : BinaryTriangularPointCoordinates G X 4)

theorem exists_actual_module_operator_leading_subset
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (v : W.toRepresentation.asModule) (a b : Fin 16)
    (hv : FiniteRowLeadingWeight.HasLeading (T.subrepresentationModuleCoordinates W v) a)
    (hba : support b ⊆ support a) :
    ∃ r : (ZMod 2)[G], FiniteRowLeadingWeight.HasLeading
      (T.subrepresentationModuleCoordinates W (r • v)) b := by
  letI : AddCommGroup W.toRepresentation.asModule := inferInstanceAs (AddCommGroup W.toSubmodule)
  letI : Module (ZMod 2)[G] W.toRepresentation.asModule :=
    W.toRepresentation.instModuleMonoidAlgebraAsModule
  apply exists_operator_leading_subset_of_leading_derivatives
    (T.subrepresentationModuleCoordinates W) _ v a b hv hba
  intro i z a hz hi
  obtain ⟨g, hg⟩ := T.actual_leading_derivative W i (W.toRepresentation.asModuleEquiv z) a hz hi
  refine ⟨MonoidAlgebra.single g (1 : ZMod 2) - 1, ?_⟩
  rw [sub_smul, Representation.single_smul, one_smul, one_smul]
  exact hg

theorem exists_head_four_minimum_generators
    (hG : IsPGroup 2 G)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (hhead : Module.finrank (ZMod 2)
      (W.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) = 4) :
    ∃ (v : Fin 4 → W.toRepresentation.asModule) (label : Fin 4 → Fin 16),
      Submodule.span (ZMod 2)[G] (Set.range v) = ⊤ ∧
      (∀ i, v i ≠ 0 ∧ FiniteRowLeadingWeight.HasLeading
        (T.subrepresentationModuleCoordinates W (v i)) (label i)) ∧
      Function.Injective label ∧
      (∀ i j, i ≠ j → ∀ r : (ZMod 2)[G], ¬FiniteRowLeadingWeight.HasLeading
        (T.subrepresentationModuleCoordinates W (r • v i)) (label j)) ∧
      (∀ i j, i ≠ j → ¬support (label j) ⊆ support (label i)) := by
  letI : AddCommGroup W.toRepresentation.asModule := inferInstanceAs (AddCommGroup W.toSubmodule)
  letI : Module (ZMod 2)[G] W.toRepresentation.asModule :=
    W.toRepresentation.instModuleMonoidAlgebraAsModule
  letI : Finite W.toSubmodule := Finite.of_injective W.toSubmodule.subtype W.toSubmodule.injective_subtype
  have hd := pGroup_representationGeneratedBy_coinvariants hG W.toRepresentation
  rw [← representationHead_finrank_eq_coinvariants, hhead] at hd
  have hC : Function.Injective (T.subrepresentationModuleCoordinates W) :=
    (T.subrepresentationCoordinates_injective W).comp W.toRepresentation.asModuleEquiv.injective
  have hneed : ∀ S : Finset W.toRepresentation.asModule,
      Submodule.span (ZMod 2)[G] (S : Set W.toRepresentation.asModule) = ⊤ → 4 ≤ S.card := by
    intro S hS
    obtain ⟨u, hu⟩ := ModuleGeneratedBy.of_finset_card_le S hS S.card le_rfl
    have hb := representationHead_finrank_le_generators W.toRepresentation u hu
    rwa [hhead] at hb
  obtain ⟨v, label, hv, hlead, hinj, hcollision⟩ :=
    exists_minimum_four_nonzero_generators_no_collision hd
      (T.subrepresentationModuleCoordinates W) hC 0 hneed
  refine ⟨v, label, hv, hlead, hinj, hcollision, ?_⟩
  intro i j hij hsub
  obtain ⟨r, hr⟩ := T.exists_actual_module_operator_leading_subset W (v i)
    (label i) (label j) (hlead i).2 hsub
  exact hcollision i j hij r hr

end SymmetricSubgroupAsymptotics.BinaryTriangularPointCoordinates
