import SymmetricSubgroupAsymptotics.GaronziMarotiMathieuTwelveResidualReduction
import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveClassTail
import SymmetricSubgroupAsymptotics.CFSGNonaffinePrimitivePolylogRank

/-! Partial GM progress: every remaining actual primitive finite-model
counterexample has bounded degree, with one internally constructed cutoff.
Original small-fibre, component, top and nested-refinement witnesses remain
unchanged. The SAME original D/e/index degree forms are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GaronziMarotiFinitePrimitiveBoundedResidual
open PrimitiveSocleRawStructure
open GaronziMarotiMathieuTwelveResidualReduction

/-- Exactly Tits and the24 sporadics other than M11/M12. -/
abbrev Menu := {j : Option CFSG.Sporadic // j≠some .m11 ∧ j≠some .m12}

def menuIndex (j : Menu) : CFSG.Index := match j.val with
  | none => .tits
  | some s => .sporadic s

def model (j : Menu) : Type := (menuIndex j).Model
instance (j : Menu) : Group (model j) := CFSG.Index.instGroupModel (menuIndex j)

theorem menu_card : Nat.card Menu=25 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem exists_remaining_threshold :
    ∃ N : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      (D : NonaffineData G X) (i : CFSG.Index), RemainingFiniteSimpleType i →
      (D.Simple ≃* i.Model) → N≤Nat.card X →
      ∀ H : Subgroup G,Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  obtain ⟨N,hN⟩ := FiniteModelPrimitiveClassTail.finite_family_threshold model
  refine ⟨N,?_⟩
  intro G X _ _ _ _ D i hi e hn H
  cases i <;> try { exact hi.1.elim }
  case tits =>
    exact hN ⟨none,by simp⟩ D e hn H
  case sporadic s =>
    have hs11 : some s≠some CFSG.Sporadic.m11 := by
      intro h
      apply hi.2.1
      exact congrArg CFSG.Index.sporadic (Option.some.inj h)
    have hs12 : some s≠some CFSG.Sporadic.m12 := by
      intro h
      apply hi.2.2
      exact congrArg CFSG.Index.sporadic (Option.some.inj h)
    exact hN ⟨some s,hs11,hs12⟩ D e hn H

variable (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]

/-- The original nonprimitive finite-model alternatives are literal. -/
def ActualFiniteModelResidual (N : ℕ) : Prop :=
  (Nat.card X<N ∧ GaronziMarotiMathieuTwelveResidualReduction.PrimitiveFiniteModelResidual G X) ∨
    ∃ ht : MulAction.IsPretransitive G X,
      letI := ht
      ∃ ω₀ : X, ∃ D : OriginalMinimalBlock (A := G) ω₀,
        GaronziMarotiMathieuTwelveResidualReduction.OriginalFiniteModelResidual D

private theorem refine_finite_residual (N : ℕ)
    (hN : ∀ {B Y : Type} [Group B] [Finite B] [Finite Y] [MulAction B Y]
      (D : NonaffineData B Y) (i : CFSG.Index), RemainingFiniteSimpleType i →
      (D.Simple ≃* i.Model) → N≤Nat.card Y →
      ∀ H : Subgroup B,Nat.card (ConjClasses H)^3≤5^(Nat.card Y-1))
    (hbad : 5^(Nat.card X-1)<Nat.card (ConjClasses G)^3)
    (h : GaronziMarotiMathieuTwelveResidualReduction.ActualFiniteModelResidual G X) :
    ActualFiniteModelResidual G X N := by
  rcases h with h | h
  · left
    refine ⟨?_,h⟩
    by_contra hlarge
    obtain ⟨hp,D,i,⟨e⟩,hi,hform⟩ := h
    have hh := hN D i hi e (by omega) (⊤ : Subgroup G)
    have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    rw [he] at hh
    exact (not_lt_of_ge hh hbad).elim
  · exact Or.inr h

/-- No class/count/model hypothesis is introduced. -/
theorem garonziMaroti_or_bounded_primitive_or_original_residual
    (hCFSG : CFSG.CFSGClassification) :
    ∃ N : ℕ, GaronziMarotiConjugacyClassBound ∨
      (∃ n : ℕ,4≤n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5^(n-1)<Nat.card (ConjClasses L)^3 ∧ ActualSmallFibreResidual L (Fin n)) ∨
      (∃ n : ℕ,4≤n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5^(n-1)<Nat.card (ConjClasses L)^3 ∧ ActualBoundedNonaffineResidual L (Fin n)) ∨
      (∃ n : ℕ,4≤n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5^(n-1)<Nat.card (ConjClasses L)^3 ∧ ActualFiniteModelResidual L (Fin n) N) := by
  obtain ⟨N,hN⟩ := exists_remaining_threshold
  refine ⟨N,?_⟩
  rcases garonziMaroti_or_actual_shape_counterexample_or_finite_model hCFSG with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · obtain ⟨n,hn,L,hbad,h⟩ := h
    refine Or.inr (Or.inr (Or.inr ⟨n,hn,L,hbad,?_⟩))
    exact refine_finite_residual L (Fin n) N hN (by simpa only [Nat.card_fin] using hbad) h

end SymmetricSubgroupAsymptotics.GaronziMarotiFinitePrimitiveBoundedResidual
