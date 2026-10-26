import SymmetricSubgroupAsymptotics.GaronziMarotiNonaffineShapeCFSGReduction
import SymmetricSubgroupAsymptotics.CFSGMathieuElevenClassResidualReduction

/-! Cumulative original-action adapter. All older shape exclusions are
retained literally. An M11 nonaffine top or component is paid by the
closed consumers, without classifying an imprimitive top. The unbounded
original-action residual is retained verbatim; its index-order-failure
witness cannot have model M11, as shown separately below. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GaronziMarotiMathieuElevenResidualReduction
open PrimitiveSocleRawStructure

variable (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

def ActualSmallFibreResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive G X,
    letI := ht
    ∃ ω₀ : X, ∃ D : OriginalMinimalBlock (A := G) ω₀,
      OriginalMinimalBlockNonaffineShapeResidual.SmallFibreShape D ∧
      ¬ SmallFibreKnownModelGlobalClassGap.HasClosedTop D ∧
      5 ≤ Nat.card D.Points ∧
      (5 ≤ Nat.card D.Points → ¬ Nonempty (PrimitiveAffineProfile D.Top D.Points)) ∧
      ¬ ∃ E : NonaffineData D.Top D.Points,
        Nonempty (E.Simple ≃* CFSG.Models.Presentations.M11.Model)

def ActualBoundedNonaffineResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive G X,
    letI := ht
    ∃ ω₀ : X, ∃ D : OriginalMinimalBlock (A := G) ω₀,
      OriginalMinimalBlockNonaffineShapeResidual.BoundedNonaffineComponent D ∧
      ¬ ∃ E : NonaffineData D.Component D.Fibre,
        Nonempty (E.Simple ≃* CFSG.Models.Presentations.M11.Model)

def PrimitiveFiniteModelResidual : Prop :=
  MulAction.IsPreprimitive G X ∧
    ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
      Nonempty (D.Simple ≃* i.Model) ∧
      CFSGMathieuElevenClassResidualReduction.RemainingFiniteSimpleType i ∧
      ((∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index ^ D.factorCount) ∨
        (∃ a : ℕ, D.factorCount ≤ 2*a ∧ Nat.card X = (Nat.card D.Simple)^a))

def ActualFiniteModelResidual : Prop :=
  PrimitiveFiniteModelResidual G X ∨
    ∃ ht : MulAction.IsPretransitive G X,
      letI := ht
      ∃ ω₀ : X, ∃ D : OriginalMinimalBlock (A := G) ω₀,
        OriginalMinimalBlockBoundedShapeResidual.ActualFiniteModelResidual D

/-- Applies to each literal component/top/refinement tuple in the retained
original-action residual. No change of its subgroup or action is needed. -/
theorem not_m11_of_index_order_failure
    {B Y : Type} [Group B] [Finite B] [Finite Y] [MulAction B Y]
    (E : NonaffineData B Y) (i : CFSG.Index) (e : E.Simple ≃* i.Model)
    (K : Subgroup E.Simple) (hK : K ≠ ⊤)
    (hfail : K.index ^ 66 < Nat.card E.Simple * Nat.card (Outer E.Simple)) :
    i ≠ .sporadic .m11 := by
  intro hm
  subst i
  letI : Finite CFSG.Models.Presentations.M11.Model := Finite.of_equiv E.Simple e.toEquiv
  letI : IsSimpleGroup CFSG.Models.Presentations.M11.Model := e.symm.isSimpleGroup
  have hmap : K.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hi := CFSGMathieuElevenMinimumIndex.proper_index_ge_eleven
    (K.map e.toMonoidHom) hmap
  have hiEq : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
  have hidx : 11 ≤ K.index := hi.trans (Nat.le_of_eq hiEq)
  have hc : Nat.card E.Simple = 7920 :=
    (Nat.card_congr e.toEquiv).trans CFSGMathieuElevenActualEquivalence.card
  have ho : Nat.card (Outer E.Simple) ≤ 1 := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGMathieuElevenOuterBound.outer_card_le_one
  have hupper : Nat.card E.Simple * Nat.card (Outer E.Simple) ≤ 7920 := by
    rw [hc]
    simpa using Nat.mul_le_mul_left 7920 ho
  have hlower : 7920 < K.index ^ 66 := by
    calc
      7920 < 11 ^ 4 := by norm_num
      _ ≤ K.index ^ 4 := Nat.pow_le_pow_left hidx 4
      _ ≤ K.index ^ 66 := Nat.pow_le_pow_right (by omega) (by decide)
  exact (not_lt_of_ge hupper (hlower.trans hfail)).elim

theorem class_cube_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hn : 4 ≤ Nat.card X)
    (hSmaller : ∀ m : ℕ, m < Nat.card X → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L)^3 ≤ 5^(m-1)) :
    Nat.card (ConjClasses G)^3 ≤ 5^(Nat.card X-1) ∨
      ActualSmallFibreResidual G X ∨ ActualBoundedNonaffineResidual G X ∨
        ActualFiniteModelResidual G X := by
  by_cases hpaid : Nat.card (ConjClasses G)^3 ≤ 5^(Nat.card X-1)
  · exact Or.inl hpaid
  right
  rcases GaronziMarotiNonaffineShapeCFSGReduction.class_cube_or_actual_small_fibre_or_nonaffine_component_or_finite_model
      G X hCFSG hn hSmaller with h | h | h | h
  · exact (hpaid h).elim
  · obtain ⟨ht,ω₀,D,hshape,hclosed,htop,haffine⟩ := h
    letI := ht
    refine Or.inl ⟨ht,ω₀,D,hshape,hclosed,htop,haffine,?_⟩
    rintro ⟨E,⟨e⟩⟩
    have hh := CFSGMathieuElevenCompleteClassConsumers.original_small_fibre_subnormal_gap
      D.map D.map_equivariant (Nat.card D.Fibre) hshape.1 D.fibre_card_at E e
      (⊤ : Subgroup G) (Subgroup.Normal.isSubnormal inferInstance)
    have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    rw [he] at hh
    exact hpaid (hh.trans (Nat.pow_le_pow_right (by decide : 0 < 5) (by omega)))
  · obtain ⟨ht,ω₀,D,hshape⟩ := h
    letI := ht
    refine Or.inr (Or.inl ⟨ht,ω₀,D,hshape,?_⟩)
    rintro ⟨E,⟨e⟩⟩
    exact hpaid (CFSGMathieuElevenCompleteClassConsumers.original_component_class_cube
      D E e (by have := hshape.2.1; omega) hSmaller)
  · right; right
    rcases h with ⟨hp,D,i,⟨e⟩,hi,hform⟩ | h
    · by_cases hm : i = .sporadic .m11
      · subst i
        have hh := CFSGMathieuElevenCompleteClassConsumers.primitive_subnormal_class_cube
          D e (⊤ : Subgroup G) (Subgroup.Normal.isSubnormal inferInstance)
        have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
        rw [he] at hh
        exact (hpaid hh).elim
      · exact Or.inl ⟨hp,D,i,⟨e⟩,⟨hi,hm⟩,hform⟩
    · exact Or.inr h

theorem minimal_counterexample_has_actual_residual
    (hCFSG : CFSG.CFSGClassification)
    (n : ℕ) (hn : 4 ≤ n) (L : Subgroup (Equiv.Perm (Fin n)))
    (hbad : 5^(n-1) < Nat.card (ConjClasses L)^3)
    (hSmaller : ∀ m : ℕ, m < n → 4 ≤ m →
      ∀ H : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses H)^3 ≤ 5^(m-1)) :
    ActualSmallFibreResidual L (Fin n) ∨ ActualBoundedNonaffineResidual L (Fin n) ∨
      ActualFiniteModelResidual L (Fin n) := by
  have hs : ∀ m : ℕ, m < Nat.card (Fin n) → 4 ≤ m →
      ∀ H : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses H)^3 ≤ 5^(m-1) := by
    simpa only [Nat.card_fin] using hSmaller
  rcases class_cube_or_actual_residual L (Fin n) hCFSG
      (by simpa only [Nat.card_fin] using hn) hs with h | h
  · have hc : Nat.card (ConjClasses L)^3 ≤ 5^(n-1) := by
      simpa only [Nat.card_fin] using h
    exact (not_lt_of_ge hc hbad).elim
  · exact h

end SymmetricSubgroupAsymptotics.GaronziMarotiMathieuElevenResidualReduction
