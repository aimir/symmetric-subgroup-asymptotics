import SymmetricSubgroupAsymptotics.TerminalIncidenceCohomology

/-!
# Joint quadratic incidence modulo an actual allowable subspace

The allowable outcome space is kept as a literal subspace throughout the
pivot argument. Passing to its cardinality occurs only after each quotient
outcome fibre has been counted by actual quadratic realization fibres.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [local instance] Fintype.ofFinite

local instance {D F : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    [AddCommGroup F] [Module (ZMod 2) F] [Finite D] [Finite F] :
    Finite (D →ₗ[ZMod 2] F) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

local instance {D F : Type*} [AddCommGroup D] [Module (ZMod 2) D]
    [AddCommGroup F] [Module (ZMod 2) F] [Finite D] [Finite F]
    (Q : QuadraticForm (ZMod 2) D) (q : QuadraticForm (ZMod 2) F) :
    Finite (QuadraticRealizations Q q) := by
  unfold QuadraticRealizations
  infer_instance

/-- Passing to an outcome modulo an actual subspace costs its exact number
of possible representatives. -/
theorem terminal_quotient_outcome_count_le {X Y : Type*} [Finite X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]
    (S : Submodule (ZMod 2) Y) (q : X → Y) (M : ℕ)
    (hM : ∀ y, Nat.card {x : X // q x=y} ≤ M) (v : Y ⧸ S) :
    Nat.card {x : X // S.mkQ (q x)=v} ≤ Nat.card S * M := by
  by_cases hn : Nonempty {x : X // S.mkQ (q x)=v}
  · let x₀ := Classical.choice hn
    let encode : {x : X // S.mkQ (q x)=v} →
        Σ s : S, {x : X // q x=q x₀.1+s.1} := fun x =>
      ⟨⟨q x.1-q x₀.1,by
        apply (Submodule.Quotient.mk_eq_zero S).mp
        change S.mkQ (q x.1-q x₀.1)=0
        rw [map_sub,x.2,x₀.2,sub_self]⟩,⟨x.1,by change q x.1=q x₀.1+(q x.1-q x₀.1); abel⟩⟩
    have hinj : Function.Injective encode := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z => z.2.1) h
    calc
      _ ≤ Nat.card (Σ s : S, {x : X // q x=q x₀.1+s.1}) :=
        Nat.card_le_card_of_injective encode hinj
      _ = ∑ s : S, Nat.card {x : X // q x=q x₀.1+s.1} := Nat.card_sigma
      _ ≤ ∑ _s : S, M := Finset.sum_le_sum (fun s _ => hM _)
      _ = _ := by simp [← Nat.card_eq_fintype_card]
  · haveI : IsEmpty {x : X // S.mkQ (q x)=v} := not_nonempty_iff.mp hn
    rw [Nat.card_eq_zero.mpr (Or.inl inferInstance)]
    exact Nat.zero_le _

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]

/-- The exact quadratic outcome, as a pointwise function on the complete
domain of a surjective coordinate map. -/
def terminalQuadraticOutcome {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) V) (f : SurjectiveBinaryMaps E V) : E → ZMod 2 :=
  fun x => q (f.1 x)

/-- The function-valued outcome fibre is genuinely a quadratic realization
fibre whenever it is nonempty. -/
theorem terminal_quadratic_outcome_count_le {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (Q : E → ZMod 2) :
    Nat.card {f : SurjectiveBinaryMaps E V // terminalQuadraticOutcome q f=Q} ≤
      Nat.card (q.IsometryEquiv q) := by
  by_cases hn : Nonempty {f : SurjectiveBinaryMaps E V // terminalQuadraticOutcome q f=Q}
  · let f₀ := Classical.choice hn
    let encode : {f : SurjectiveBinaryMaps E V // terminalQuadraticOutcome q f=Q} →
        QuadraticRealizations (q.comp f₀.1.1) q := fun f =>
      ⟨f.1.1,f.1.2,by
        ext x
        exact congrFun (f.2.trans f₀.2.symm) x⟩
    have hinj : Function.Injective encode := by
      intro f g h
      have h' : f.1.1 = g.1.1 := congrArg (fun z => z.1) h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.card_le_card_of_injective encode hinj).trans
      (quadraticRealization_card_le _ q hq)
  · haveI : IsEmpty {f : SurjectiveBinaryMaps E V // terminalQuadraticOutcome q f=Q} :=
      not_nonempty_iff.mp hn
    simp

variable {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
    [∀ i, Finite (V i)]

/-- Every original relation is imposed modulo the same actual allowable
outcome space, rather than testing unrelated scalar dimensions. -/
abbrev TerminalQuadraticRelationTuples (S : Submodule (ZMod 2) (E → ZMod 2))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) :=
  {f : ∀ i, SurjectiveBinaryMaps E (V i) //
    ∀ b : B, (∑ i, b.1 i • terminalQuadraticOutcome (q i) (f i)) ∈ S}

/-- Exact conversion to simultaneous zero relations in the quotient outcome
space; all coordinate maps and the relation space are retained. -/
def terminalQuadraticRelationTuplesEquiv (S : Submodule (ZMod 2) (E → ZMod 2))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) :
    TerminalQuadraticRelationTuples S B q ≃
      CoordinateRelationSolutions (quadraticRelationCoordinate B)
        (fun i f => S.mkQ (terminalQuadraticOutcome (q i) f)) :=
  Equiv.subtypeEquivRight fun f => by
    apply forall_congr'
    intro b
    change (∑ i, b.1 i • terminalQuadraticOutcome (q i) (f i)) ∈ S ↔
      ∑ i, b.1 i • S.mkQ (terminalQuadraticOutcome (q i) (f i))=0
    simp only [← map_smul]
    rw [← map_sum]
    exact (Submodule.Quotient.mk_eq_zero S).symm

/-- Joint pivot incidence with the exact allowable-space multiplicity.
In the terminal application this space is the image of the retained
inflation kernel, so its dimension is at most τ. -/
theorem terminalQuadraticRelationTuples_count_le
    (S : Submodule (ZMod 2) (E → ZMod 2))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (P : CoordinatePivotSystem (quadraticRelationCoordinate B))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (M : ℕ) (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ M) :
    Nat.card (TerminalQuadraticRelationTuples S B q) ≤
      (∏ i : {i : ι // i ∉ P.indices}, Nat.card (SurjectiveBinaryMaps E (V i.1))) *
        (Nat.card S * M)^Module.finrank (ZMod 2) B := by
  rw [Nat.card_congr (terminalQuadraticRelationTuplesEquiv S B q)]
  apply P.solution_count_le
  intro i Q
  exact terminal_quotient_outcome_count_le S (terminalQuadraticOutcome (q i)) M
    (fun Q => (terminal_quadratic_outcome_count_le (q i) (hq i) Q).trans (hM i)) Q

section TotalMaps

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

/-- Actual maps on the whole ordered record domain, with every quadratic
coordinate onto and all original relations in the retained allowable space. -/
abbrev TerminalQuadraticRelationMaps (S : Submodule (ZMod 2) (E → ZMod 2))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) :=
  {f : E →ₗ[ZMod 2] (W × ∀ i, V i) //
    (∀ i, Function.Surjective (fun x => (f x).2 i)) ∧
    ∀ b : B, (fun x => ∑ i, b.1 i * q i ((f x).2 i)) ∈ S}

private def terminalQuadraticRelationMapEncode
    (S : Submodule (ZMod 2) (E → ZMod 2))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (f : TerminalQuadraticRelationMaps (W := W) S B q) :
    (E →ₗ[ZMod 2] W) × TerminalQuadraticRelationTuples S B q :=
  ⟨(LinearMap.fst _ _ _).comp f.1,
    ⟨fun i => ⟨quadraticCoordinateMap f.1 i,f.2.1 i⟩,by
      intro b
      convert f.2.2 b using 1
      ext x
      simp [terminalQuadraticOutcome,quadraticCoordinateMap,smul_eq_mul]⟩⟩

omit [Finite E] [∀ i, Finite (V i)] [Finite W] in
private theorem terminalQuadraticRelationMapEncode_injective
    (S : Submodule (ZMod 2) (E → ZMod 2))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) :
    Function.Injective (terminalQuadraticRelationMapEncode (W := W) S B q) := by
  intro f g h
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun z => z.1 x) h
  · funext i
    exact congrArg (fun z => (z.2.1 i).1 x) h

/-- Exact nonpivot dimension and actual allowable-space cardinal retained. -/
theorem terminalQuadraticRelationMaps_count_le_pivots
    (S : Submodule (ZMod 2) (E → ZMod 2))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (P : CoordinatePivotSystem (quadraticRelationCoordinate B))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (M : ℕ) (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ M) :
    Nat.card (TerminalQuadraticRelationMaps (W := W) S B q) ≤
      (Nat.card S * M)^Module.finrank (ZMod 2) B *
      2^(Module.finrank (ZMod 2) E * (Module.finrank (ZMod 2) W +
        ∑ i : {i : ι // i ∉ P.indices}, Module.finrank (ZMod 2) (V i.1))) := by
  have ht := terminalQuadraticRelationTuples_count_le S B P q hq M hM
  have hp : (∏ i : {i : ι // i ∉ P.indices}, Nat.card (SurjectiveBinaryMaps E (V i.1))) ≤
      2^(Module.finrank (ZMod 2) E *
        ∑ i : {i : ι // i ∉ P.indices}, Module.finrank (ZMod 2) (V i.1)) := by
    calc
      _ ≤ ∏ i : {i : ι // i ∉ P.indices},
          2^(Module.finrank (ZMod 2) E * Module.finrank (ZMod 2) (V i.1)) :=
        Finset.prod_le_prod' (fun _ _ => surjectiveBinaryMaps_count_le)
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum,Finset.mul_sum]
  calc
    _ ≤ Nat.card ((E →ₗ[ZMod 2] W) × TerminalQuadraticRelationTuples S B q) :=
      Nat.card_le_card_of_injective (terminalQuadraticRelationMapEncode S B q)
        (terminalQuadraticRelationMapEncode_injective S B q)
    _ = Nat.card (E →ₗ[ZMod 2] W) * Nat.card (TerminalQuadraticRelationTuples S B q) :=
      Nat.card_prod _ _
    _ ≤ Nat.card (E →ₗ[ZMod 2] W) *
        (2^(Module.finrank (ZMod 2) E *
          ∑ i : {i : ι // i ∉ P.indices}, Module.finrank (ZMod 2) (V i.1)) *
          (Nat.card S * M)^Module.finrank (ZMod 2) B) :=
      Nat.mul_le_mul_left _ (ht.trans (Nat.mul_le_mul_right _ hp))
    _ = _ := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap]
      simp only [Nat.card_zmod]
      rw [Nat.mul_add,pow_add]
      ring

/-- Complete ordered-map incidence: one factor `M·2^τ` per pivot and at
least two lost target dimensions per retained independent relation. -/
theorem terminalQuadraticRelationMaps_count_le
    (S : Submodule (ZMod 2) (E → ZMod 2))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (hv : ∀ i, 2 ≤ Module.finrank (ZMod 2) (V i))
    (M τ : ℕ) (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ M)
    (hτ : Module.finrank (ZMod 2) S ≤ τ) :
    Nat.card (TerminalQuadraticRelationMaps (W := W) S B q) ≤
      (M * 2^τ)^Module.finrank (ZMod 2) B *
      2^(Module.finrank (ZMod 2) E * (Module.finrank (ZMod 2) W +
        ∑ i, Module.finrank (ZMod 2) (V i) - 2*Module.finrank (ZMod 2) B)) := by
  let P := quadraticRelationPivots B
  have hS : Nat.card S ≤ 2^τ := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    simp only [Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hτ
  have hp : 2 * Module.finrank (ZMod 2) B ≤
      ∑ i : P.indices, Module.finrank (ZMod 2) (V i.1) := by
    calc
      _ = ∑ _i : P.indices, 2 := by simp [P.card_indices,Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hv i.1)
  have hsplit : (∑ i : P.indices, Module.finrank (ZMod 2) (V i.1)) +
      (∑ i : {i : ι // i ∉ P.indices}, Module.finrank (ZMod 2) (V i.1)) =
        ∑ i, Module.finrank (ZMod 2) (V i) :=
    Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ P.indices)
      (fun i => Module.finrank (ZMod 2) (V i))
  refine (terminalQuadraticRelationMaps_count_le_pivots S B P q hq M hM).trans ?_
  apply Nat.mul_le_mul
  · apply Nat.pow_le_pow_left
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right M hS
  · apply Nat.pow_le_pow_right (by decide)
    apply Nat.mul_le_mul_left
    omega

end TotalMaps

end SymmetricSubgroupAsymptotics
