import SymmetricSubgroupAsymptotics.OriginalMinimalBlockBoundedShapeResidual
import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeFFourCompleteCFSGReduction
import SymmetricSubgroupAsymptotics.GaronziMarotiIntransitiveReduction
import SymmetricSubgroupAsymptotics.BinaryEightBlockClassInduction

/-! A global induction step with an honest bounded-shape residual.
No bounded-degree class estimate is supplied. Any minimal counterexample
must itself have bounded degree or retain a literal original-action
Tits/sporadic obstruction, including its actual degree forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GaronziMarotiBoundedShapeCFSGReduction
open PrimitiveSocleRawStructure

variable (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

def PrimitiveFiniteModelResidual : Prop :=
  MulAction.IsPreprimitive G X ∧
    ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
      Nonempty (D.Simple ≃* i.Model) ∧
      PrimitiveAllDegreeReeFFourCompleteCFSGReduction.RemainingFiniteSimpleType i ∧
      ((∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index ^ D.factorCount) ∨
        (∃ a : ℕ, D.factorCount ≤ 2*a ∧ Nat.card X = (Nat.card D.Simple)^a))

def ActualFiniteModelResidual : Prop :=
  PrimitiveFiniteModelResidual G X ∨
    ∃ ht : MulAction.IsPretransitive G X,
      letI := ht
      ∃ ω₀ : X, ∃ D : OriginalMinimalBlock (A := G) ω₀,
        OriginalMinimalBlockBoundedShapeResidual.ActualFiniteModelResidual D

theorem class_cube_or_bounded_degree_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification) (hn : 4 ≤ Nat.card X)
    (hSmaller : ∀ m : ℕ, m < Nat.card X → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L)^3 ≤ 5^(m-1)) :
    Nat.card (ConjClasses G)^3 ≤ 5^(Nat.card X-1) ∨
      Nat.card X ≤ 36855 ∨ ActualFiniteModelResidual G X := by
  by_cases ht : MulAction.IsPretransitive G X
  · letI := ht
    letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    by_cases hp : MulAction.IsPreprimitive G X
    · letI := hp
      rcases PrimitiveAllDegreeReeFFourCompleteCFSGReduction.primitive_subnormal_cube_or_finite_model
        hCFSG G X hn ⊤ (Subgroup.Normal.isSubnormal inferInstance) with h | h
      · have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
        rw [he] at h
        exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl ⟨hp,h⟩))
    · let ω₀ : X := Classical.choice inferInstance
      obtain ⟨D⟩ := originalMinimalBlock_nonempty ω₀ hp
      rcases OriginalMinimalBlockBoundedShapeResidual.class_cube_or_bounded_shape_or_actual_finite_model
        D hCFSG hSmaller with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr ⟨ht,ω₀,D,h⟩))
  · exact Or.inl
      (GaronziMarotiIntransitiveReduction.intransitive_step ht hn hSmaller)

theorem minimal_counterexample_bounded_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification)
    (n : ℕ) (hn : 4 ≤ n) (L : Subgroup (Equiv.Perm (Fin n)))
    (hbad : 5^(n-1) < Nat.card (ConjClasses L)^3)
    (hSmaller : ∀ m : ℕ, m < n → 4 ≤ m →
      ∀ H : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses H)^3 ≤ 5^(m-1)) :
    n ≤ 36855 ∨ ActualFiniteModelResidual L (Fin n) := by
  have hs : ∀ m : ℕ, m < Nat.card (Fin n) → 4 ≤ m →
      ∀ H : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses H)^3 ≤ 5^(m-1) := by
    simpa only [Nat.card_fin] using hSmaller
  rcases class_cube_or_bounded_degree_or_actual_finite_model L (Fin n) hCFSG
    (by simpa only [Nat.card_fin] using hn) hs with h | h | h
  · have hc : Nat.card (ConjClasses L)^3 ≤ 5^(n-1) := by
      simpa only [Nat.card_fin] using h
    exact (not_lt_of_ge hc hbad).elim
  · exact Or.inl (by simpa only [Nat.card_fin] using h)
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.GaronziMarotiBoundedShapeCFSGReduction
