import SymmetricSubgroupAsymptotics.CFSGOrthogonalDFourOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDFourSufficientSimpleIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDHigherRankSimpleIndexReduction

/-! The sufficient internal simple-index boundary is proved for ALL
original untwisted classical models, including D4 in every characteristic.
It retains coefficient three at the small frontier and uses coefficient
six only where the checked primitive consumers permit it. Other original
models remain explicit; neither the stronger published theorem nor the
whole CFSG-only T1 theorem is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

def ModelSufficientSimpleIndexBounds (i : CFSG.Index) : Prop :=
  ∀ ell : ℕ, LeastProperIndex i.Model ell → ell^2 < Nat.card i.Model ∧
    SufficientOuterOrderBudget ell (Nat.card (Outer i.Model))

theorem modelSufficientSimpleIndexBounds_of_sharp (i : CFSG.Index)
    [Finite i.Model] [IsSimpleGroup i.Model] (hn : ¬IsMulCommutative i.Model)
    (h : ModelSimpleIndexBounds i) : ModelSufficientSimpleIndexBounds i := by
  intro ell he
  obtain ⟨hs,ho⟩ := h ell he
  have hf : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun hc => hn (isMulCommutative_iff.mpr hc)) he.1
  exact ⟨hs,SufficientOuterOrderBudget.of_sharp hf ho⟩

theorem typeD_four_sufficientSimpleIndexBudget (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D 4 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.D 4 q) ell) :
    ell^2 < Nat.card (CFSG.Models.D 4 q) ∧
      SufficientOuterOrderBudget ell (Nat.card (Outer (CFSG.Models.D 4 q))) :=
  typeD_four_sufficientSimpleIndexBudget_of_outer q ell hell
    (typeD_four_outer_card_le q) (typeD_four_binary_outer_card_le q)

def RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki : CFSG.Index → Prop
  | .D _ _ _ => False
  | i => RemainingSimpleIndexModelWithoutTypeASuzukiCBDHigh i

theorem sufficientSimpleIndex_model_or_remaining_without_classical_suzuki
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) :
    ModelSufficientSimpleIndexBounds i ∨
      RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i := by
  cases i <;> try
    exact (simpleIndex_model_or_remaining_without_typeA_suzuki_C_B_DHigh _ hn).imp
      (fun h => modelSufficientSimpleIndexBounds_of_sharp _ hn h) id
  case D r q hr hfinite hsimple =>
    letI : IsSimpleGroup (CFSG.Models.D r q) := hsimple
    by_cases hfour : r=4
    · subst r
      exact Or.inl (typeD_four_sufficientSimpleIndexBudget q)
    · left
      exact modelSufficientSimpleIndexBounds_of_sharp _ hn
        (typeD_high_simpleIndexBounds r (by omega) q)

theorem sufficientSimpleIndexBounds_of_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H)
    (hH : ∀ ell : ℕ, LeastProperIndex H ell → ell^2 < Nat.card H ∧
      SufficientOuterOrderBudget ell (Nat.card (Outer H))) :
    ∀ ell : ℕ, LeastProperIndex G ell → ell^2 < Nat.card G ∧
      SufficientOuterOrderBudget ell (Nat.card (Outer G)) := by
  intro ell hell
  have h := hH ell (leastProperIndex_of_mulEquiv e ell hell)
  simpa only [Nat.card_congr e.toEquiv,outer_card_congr e] using h

theorem sufficientSimpleIndexBounds_of_cfsg_and_remaining_nonclassical_models
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀(i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i →
        ModelSufficientSimpleIndexBounds i) : SufficientSimpleIndexBounds := by
  intro G _ _ _ hn
  apply of_nonabelian_simple_models hCFSG
    (fun H => ∀ ell : ℕ, LeastProperIndex H ell → ell^2 < Nat.card H ∧
      SufficientOuterOrderBudget ell (Nat.card (Outer H)))
    (fun e => sufficientSimpleIndexBounds_of_mulEquiv e) ?_ G hn
  intro i _ _ hni
  rcases sufficientSimpleIndex_model_or_remaining_without_classical_suzuki i hni with h | h
  · exact h
  · exact remaining i hni h

end SymmetricSubgroupAsymptotics.CFSGReduction
