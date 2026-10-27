import SymmetricSubgroupAsymptotics.GaronziMarotiMathieuElevenResidualReduction
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveCompleteClassConsumers
import SymmetricSubgroupAsymptotics.GaronziMarotiGlobalBoundedCounterexample

/-! Cumulative original-action GM frontier with actual M11 and M12 removed.
All previous small-fibre and bounded-component guards are retained.
Unbounded component/top/refinement witnesses retain their literal groups,
subnormal subgroups, selected model equivalences and failed index budgets;
their SAME selected tags now explicitly exclude M11 and M12. The closed
M12 consumers supply each finite class step, with no new GM callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GaronziMarotiMathieuTwelveResidualReduction
open PrimitiveSocleRawStructure

def RemainingFiniteSimpleType (i : CFSG.Index) : Prop :=
  LargeTopFiniteModelResidual.RemainingFiniteSimpleType i ∧
    i ≠ .sporadic .m11 ∧ i ≠ .sporadic .m12

/-- This applies equally to every original component, top and nested
refinement model witness carrying the failed order budget. -/
theorem not_m12_of_index_order_failure
    {B Y : Type} [Group B] [Finite B] [Finite Y] [MulAction B Y]
    (E : NonaffineData B Y) (i : CFSG.Index) (e : E.Simple ≃* i.Model)
    (K : Subgroup E.Simple) (hK : K ≠ ⊤)
    (hfail : K.index ^ 66 < Nat.card E.Simple * Nat.card (Outer E.Simple)) :
    i ≠ .sporadic .m12 := by
  intro hm
  subst i
  letI : Finite CFSG.Models.Presentations.M12.Model := Finite.of_equiv E.Simple e.toEquiv
  letI : IsSimpleGroup CFSG.Models.Presentations.M12.Model := e.symm.isSimpleGroup
  have hmap : K.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hi := CFSGMathieuTwelveOuterBudgetOfFixedCapacity.proper_index_ge_eleven
    (K.map e.toMonoidHom) hmap
  have hiEq : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
  have hidx : 11 ≤ K.index := hi.trans (Nat.le_of_eq hiEq)
  have hc : Nat.card E.Simple = 95040 :=
    (Nat.card_congr e.toEquiv).trans CFSGMathieuTwelveActualEquivalence.card
  have ho : Nat.card (Outer E.Simple) ≤ 5 := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGMathieuTwelveOuterBound.outer_card_le_five
  have hupper : Nat.card E.Simple * Nat.card (Outer E.Simple) ≤ 475200 := by
    rw [hc]
    exact Nat.mul_le_mul_left 95040 ho
  have hlower : 475200 < K.index ^ 66 := by
    calc
      475200 < 11 ^ 6 := by decide
      _ ≤ K.index ^ 6 := Nat.pow_le_pow_left hidx 6
      _ ≤ K.index ^ 66 := Nat.pow_le_pow_right (by omega) (by decide)
  exact (not_lt_of_ge hupper (hlower.trans hfail)).elim

private theorem remaining_of_index_order_failure
    {B Y : Type} [Group B] [Finite B] [Finite Y] [MulAction B Y]
    (E : NonaffineData B Y) (i : CFSG.Index) (e : E.Simple ≃* i.Model)
    (hi : LargeTopFiniteModelResidual.RemainingFiniteSimpleType i)
    (K : Subgroup E.Simple) (hK : K ≠ ⊤)
    (hfail : K.index ^ 66 < Nat.card E.Simple * Nat.card (Outer E.Simple)) :
    RemainingFiniteSimpleType i :=
  ⟨hi,GaronziMarotiMathieuElevenResidualReduction.not_m11_of_index_order_failure E i e K hK hfail,
    not_m12_of_index_order_failure E i e K hK hfail⟩

section OriginalResidual
variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

def ComponentResidual : Prop :=
  (Nat.card D.Points = 2 ∨ Nat.card D.Points = 3) ∧
    ∃ x : D.Points,
      ∃ L : Subgroup (originalBlockComponent D.map D.map_equivariant x), L.IsSubnormal ∧
        ∃ E : NonaffineData (originalBlockComponent D.map D.map_equivariant x)
            (originalBlockFibre D.map x),
          ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (E.Simple ≃* i.Model) ∧
            ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card D.Fibre = K.index ^ E.factorCount ∧
              K.index ^ (4 * Nat.log 2 K.index + 23) <
                Nat.card E.Simple * Nat.card (Outer E.Simple) ∧
              K.index ^ 66 < Nat.card E.Simple * Nat.card (Outer E.Simple)

def TopResidual : Prop :=
  ∃ E : NonaffineData D.Top D.Points,
    ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (E.Simple ≃* i.Model) ∧
      ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card D.Points = K.index ^ E.factorCount ∧
        K.index ^ (4 * Nat.log 2 K.index + 23) <
          Nat.card E.Simple * Nat.card (Outer E.Simple) ∧
        K.index ^ 66 < Nat.card E.Simple * Nat.card (Outer E.Simple)

def RefinementResidual : Prop :=
  letI := D.top_pretransitive
  ∃ E : OriginalMinimalBlock (A := D.Top) D.base,
    letI := OriginalMinimalBlockTopRefinement.action D E
    (Nat.card E.Points = 2 ∨ Nat.card E.Points = 3) ∧
      ∃ y : E.Points,
        ∃ L : Subgroup (NestedBlockComponentAction.Component D.map D.map_equivariant
          (OriginalMinimalBlockTopRefinement.map D E)
          (OriginalMinimalBlockTopRefinement.map_equivariant D E) y),
        L.IsSubnormal ∧
          5 ^ (Nat.card E.Fibre * Nat.card D.Fibre - 2) < Nat.card (ConjClasses L) ^ 3 ∧
          ∃ F : NonaffineData
              (originalBlockComponent (A := A) (OriginalMinimalBlockTopRefinement.map D E)
                (OriginalMinimalBlockTopRefinement.map_equivariant D E) y)
              (originalBlockFibre (OriginalMinimalBlockTopRefinement.map D E) y),
            ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (F.Simple ≃* i.Model) ∧
              ∃ K : Subgroup F.Simple, K ≠ ⊤ ∧ Nat.card E.Fibre = K.index ^ F.factorCount ∧
                K.index ^ (4 * Nat.log 2 K.index + 23) <
                  Nat.card F.Simple * Nat.card (Outer F.Simple) ∧
                K.index ^ 66 < Nat.card F.Simple * Nat.card (Outer F.Simple)

def OriginalFiniteModelResidual : Prop :=
  ComponentResidual D ∨ TopResidual D ∨ RefinementResidual D

theorem restrict_original_finite_model
    (h : OriginalMinimalBlockBoundedShapeResidual.ActualFiniteModelResidual D) :
    OriginalFiniteModelResidual D := by
  rcases h with h | h | h
  · obtain ⟨hblocks,x,L,hL,E,i,hi,⟨e⟩,K,hK,hd,hlog,hfail⟩ := h
    exact Or.inl ⟨hblocks,x,L,hL,E,i,
      remaining_of_index_order_failure E i e hi K hK hfail,⟨e⟩,K,hK,hd,hlog,hfail⟩
  · obtain ⟨E,i,hi,⟨e⟩,K,hK,hd,hlog,hfail⟩ := h
    exact Or.inr (Or.inl ⟨E,i,
      remaining_of_index_order_failure E i e hi K hK hfail,⟨e⟩,K,hK,hd,hlog,hfail⟩)
  · letI := D.top_pretransitive
    obtain ⟨E,h⟩ := h
    letI := OriginalMinimalBlockTopRefinement.action D E
    obtain ⟨hblocks,y,L,hL,hbad,F,i,hi,⟨e⟩,K,hK,hd,hlog,hfail⟩ := h
    exact Or.inr (Or.inr ⟨E,hblocks,y,L,hL,hbad,F,i,
      remaining_of_index_order_failure F i e hi K hK hfail,⟨e⟩,K,hK,hd,hlog,hfail⟩)

end OriginalResidual

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
      (¬ ∃ E : NonaffineData D.Top D.Points,
        Nonempty (E.Simple ≃* CFSG.Models.Presentations.M11.Model)) ∧
      (¬ ∃ E : NonaffineData D.Top D.Points,
        Nonempty (E.Simple ≃* CFSG.Models.Presentations.M12.Model))

def ActualBoundedNonaffineResidual : Prop :=
  ∃ ht : MulAction.IsPretransitive G X,
    letI := ht
    ∃ ω₀ : X, ∃ D : OriginalMinimalBlock (A := G) ω₀,
      OriginalMinimalBlockNonaffineShapeResidual.BoundedNonaffineComponent D ∧
      (¬ ∃ E : NonaffineData D.Component D.Fibre,
        Nonempty (E.Simple ≃* CFSG.Models.Presentations.M11.Model)) ∧
      (¬ ∃ E : NonaffineData D.Component D.Fibre,
        Nonempty (E.Simple ≃* CFSG.Models.Presentations.M12.Model))

def PrimitiveFiniteModelResidual : Prop :=
  MulAction.IsPreprimitive G X ∧
    ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
      Nonempty (D.Simple ≃* i.Model) ∧ RemainingFiniteSimpleType i ∧
      ((∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index ^ D.factorCount) ∨
        (∃ a : ℕ, D.factorCount ≤ 2 * a ∧ Nat.card X = (Nat.card D.Simple) ^ a))

def ActualFiniteModelResidual : Prop :=
  PrimitiveFiniteModelResidual G X ∨
    ∃ ht : MulAction.IsPretransitive G X,
      letI := ht
      ∃ ω₀ : X, ∃ D : OriginalMinimalBlock (A := G) ω₀,
        OriginalFiniteModelResidual D

theorem class_cube_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (hn : 4 ≤ Nat.card X)
    (hSmaller : ∀ m : ℕ, m < Nat.card X → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    Nat.card (ConjClasses G) ^ 3 ≤ 5 ^ (Nat.card X - 1) ∨
      ActualSmallFibreResidual G X ∨ ActualBoundedNonaffineResidual G X ∨
        ActualFiniteModelResidual G X := by
  by_cases hpaid : Nat.card (ConjClasses G) ^ 3 ≤ 5 ^ (Nat.card X - 1)
  · exact Or.inl hpaid
  right
  rcases GaronziMarotiMathieuElevenResidualReduction.class_cube_or_actual_residual
      G X hCFSG hn hSmaller with h | h | h | h
  · exact (hpaid h).elim
  · obtain ⟨ht,ω₀,D,hshape,hclosed,htop,haffine,hm11⟩ := h
    letI := ht
    refine Or.inl ⟨ht,ω₀,D,hshape,hclosed,htop,haffine,hm11,?_⟩
    rintro ⟨E,⟨e⟩⟩
    have hh := CFSGMathieuTwelveCompleteClassConsumers.original_small_fibre_subnormal_gap
      D.map D.map_equivariant (Nat.card D.Fibre) hshape.1 D.fibre_card_at E e
      (⊤ : Subgroup G) (Subgroup.Normal.isSubnormal inferInstance)
    have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    rw [he] at hh
    exact hpaid (hh.trans (Nat.pow_le_pow_right (by decide : 0 < 5) (by omega)))
  · obtain ⟨ht,ω₀,D,hshape,hm11⟩ := h
    letI := ht
    refine Or.inr (Or.inl ⟨ht,ω₀,D,hshape,hm11,?_⟩)
    rintro ⟨E,⟨e⟩⟩
    exact hpaid (CFSGMathieuTwelveCompleteClassConsumers.original_component_class_cube
      D E e (by have := hshape.2.1; omega) hSmaller)
  · right; right
    rcases h with ⟨hp,D,i,⟨e⟩,hi,hform⟩ | h
    · by_cases hm : i = .sporadic .m12
      · subst i
        have hh := CFSGMathieuTwelveCompleteClassConsumers.primitive_subnormal_class_cube
          D e (⊤ : Subgroup G) (Subgroup.Normal.isSubnormal inferInstance)
        have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
        rw [he] at hh
        exact (hpaid hh).elim
      · exact Or.inl ⟨hp,D,i,⟨e⟩,⟨hi.1,hi.2,hm⟩,hform⟩
    · obtain ⟨ht,ω₀,D,hD⟩ := h
      letI := ht
      exact Or.inr ⟨ht,ω₀,D,restrict_original_finite_model D hD⟩

theorem minimal_counterexample_has_actual_residual
    (hCFSG : CFSG.CFSGClassification)
    (n : ℕ) (hn : 4 ≤ n) (L : Subgroup (Equiv.Perm (Fin n)))
    (hbad : 5 ^ (n - 1) < Nat.card (ConjClasses L) ^ 3)
    (hSmaller : ∀ m : ℕ, m < n → 4 ≤ m →
      ∀ H : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (m - 1)) :
    ActualSmallFibreResidual L (Fin n) ∨ ActualBoundedNonaffineResidual L (Fin n) ∨
      ActualFiniteModelResidual L (Fin n) := by
  have hs : ∀ m : ℕ, m < Nat.card (Fin n) → 4 ≤ m →
      ∀ H : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (m - 1) := by
    simpa only [Nat.card_fin] using hSmaller
  rcases class_cube_or_actual_residual L (Fin n) hCFSG
      (by simpa only [Nat.card_fin] using hn) hs with h | h
  · have hc : Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (n - 1) := by
      simpa only [Nat.card_fin] using h
    exact (not_lt_of_ge hc hbad).elim
  · exact h

theorem garonziMaroti_or_actual_shape_counterexample_or_finite_model
    (hCFSG : CFSG.CFSGClassification) :
    GaronziMarotiConjugacyClassBound ∨
      (∃ n : ℕ, 4 ≤ n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5 ^ (n - 1) < Nat.card (ConjClasses L) ^ 3 ∧ ActualSmallFibreResidual L (Fin n)) ∨
      (∃ n : ℕ, 4 ≤ n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5 ^ (n - 1) < Nat.card (ConjClasses L) ^ 3 ∧ ActualBoundedNonaffineResidual L (Fin n)) ∨
      (∃ n : ℕ, 4 ≤ n ∧ ∃ L : Subgroup (Equiv.Perm (Fin n)),
        5 ^ (n - 1) < Nat.card (ConjClasses L) ^ 3 ∧ ActualFiniteModelResidual L (Fin n)) := by
  by_cases hcube : ∀ n : ℕ, 4 ≤ n → ∀ L : Subgroup (Equiv.Perm (Fin n)),
      Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (n - 1)
  · left
    intro n hn L
    exact (GaronziMarotiTransitiveTarget.cube_le_iff_real_bound _ n (by omega)).mp
      (hcube n hn L)
  · push_neg at hcube
    obtain ⟨n,hn,L,hbad⟩ := hcube
    obtain ⟨m,_,hm,H,hH,hSmaller⟩ :=
      GaronziMarotiGlobalBoundedCounterexample.exists_minimal_counterexample n hn L hbad
    rcases minimal_counterexample_has_actual_residual hCFSG m hm H hH hSmaller with h | h | h
    · exact Or.inr (Or.inl ⟨m,hm,H,hH,h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m,hm,H,hH,h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m,hm,H,hH,h⟩))

end SymmetricSubgroupAsymptotics.GaronziMarotiMathieuTwelveResidualReduction
