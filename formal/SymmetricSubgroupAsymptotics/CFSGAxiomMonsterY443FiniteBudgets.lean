import SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443BinaryFacts
import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveOrdinaryBudget

/-! Concrete new-M generation and a finite-menu primitive budget. These
statements use actual literal carrier generation and generic finite-family
constants, without old classification, source orders or outer callbacks.
They do not assert that the enlarged catalogue classifies simple groups.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443FiniteBudgets
open CFSGAxiomMonsterY443ElevenGenerators PrimitiveSocleRawStructure

theorem genRank_le_eleven [Finite MonsterY443Derived] :
    MarkedC4.genRank MonsterY443Derived≤11 := by
  obtain ⟨S,hS,hcard⟩ := derived_generators
  exact (MarkedC4.genRank_le hS).trans hcard

theorem aut_card_le_pow_eleven [Finite MonsterY443Derived] :
    Nat.card (MonsterY443Derived≃*MonsterY443Derived)≤Nat.card MonsterY443Derived^11 := by
  obtain ⟨S,hS,hcard⟩ := derived_generators
  exact CFSGGeneration.aut_card_le_pow_of_generators S hS hcard

theorem sameD_simple_rank_le_eleven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple≃*MonsterY443Derived) :
    MarkedC4.genRank D.Simple≤11 := by
  letI : Finite MonsterY443Derived := Finite.of_equiv D.Simple e.toEquiv
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
  exact genRank_le_eleven

/-- The old finite Tits/sporadic menu is preserved and one actual carrier
is added. No global finiteness of the indexed carriers is required. -/
def finiteModel : Option (Option CFSG.Sporadic) → Type
  | none => MonsterY443Derived
  | some none => CFSG.Models.Tits
  | some (some s) => s.Model

instance (i : Option (Option CFSG.Sporadic)) : Group (finiteModel i) := by
  cases i with
  | none => change Group MonsterY443Derived; infer_instance
  | some i =>
    cases i with
    | none => change Group CFSG.Models.Tits; infer_instance
    | some s => change Group s.Model; infer_instance

theorem exists_uniform_primitive_finite_menu_budget :
    ∃ C : ℕ,∀ i,FiniteModelPrimitiveOrdinaryBudget.HasModelBudget (finiteModel i) C :=
  FiniteModelPrimitiveOrdinaryBudget.finite_family_budget finiteModel

end SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443FiniteBudgets
