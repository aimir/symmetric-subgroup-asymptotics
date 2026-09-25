import SymmetricSubgroupAsymptotics.CoordinateIncidence
import SymmetricSubgroupAsymptotics.HyperbolicFrames

/-!
# Joint quadratic relations among actual surjective maps

The relation space is retained as an actual subspace of the binary coordinate
space. Every pivot outcome fibre is a quadratic realization fibre, hence a
torsor for the corresponding orthogonal group when it is nonempty.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] [Finite E]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
  [∀ i, FiniteDimensional (ZMod 2) (V i)] [∀ i, Finite (V i)]

/-- Actual surjective linear maps, without quotienting by changes of basis. -/
abbrev SurjectiveBinaryMaps (E W : Type*) [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] :=
  {f : E →ₗ[ZMod 2] W // Function.Surjective f}

/-- A coordinate restricted to the retained relation subspace. -/
def quadraticRelationCoordinate (B : Submodule (ZMod 2) (ι → ZMod 2))
    (i : ι) : Module.Dual (ZMod 2) B :=
  (LinearMap.proj i).comp B.subtype

/-- Restriction of the coordinate dual basis spans the entire relation dual.
Thus every actual relation subspace admits the required pivot system. -/
theorem quadraticRelationCoordinate_span (B : Submodule (ZMod 2) (ι → ZMod 2)) :
    Submodule.span (ZMod 2) (Set.range (quadraticRelationCoordinate B)) = ⊤ := by
  have hc : quadraticRelationCoordinate B =
      B.subtype.dualMap ∘ (Pi.basisFun (ZMod 2) ι).dualBasis := by
    funext i
    ext b
    simp [quadraticRelationCoordinate, LinearMap.dualMap_apply,
      Pi.basisFun_repr]
  rw [hc, Set.range_comp, ← Submodule.map_span,
    (Pi.basisFun (ZMod 2) ι).dualBasis.span_eq, Submodule.map_top,
    LinearMap.range_eq_top]
  exact LinearMap.dualMap_surjective_of_injective B.injective_subtype

/-- A pivot system obtained from the actual relation subspace. -/
def quadraticRelationPivots (B : Submodule (ZMod 2) (ι → ZMod 2)) :
    CoordinatePivotSystem (quadraticRelationCoordinate B) :=
  coordinatePivotSystem _ (quadraticRelationCoordinate_span B)

/-- All tuples satisfying every relation in the specified subspace. -/
abbrev QuadraticRelationTuples (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) :=
  {f : ∀ i, SurjectiveBinaryMaps E (V i) //
    ∀ b : B, ∑ i, (b.1 i) • (q i).comp (f i).1 = 0}

/-- The outcome fibre really is the full quadratic realization fibre. -/
def quadraticOutcomeFibreEquiv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (q : QuadraticForm (ZMod 2) W) (Q : QuadraticForm (ZMod 2) E) :
    {f : SurjectiveBinaryMaps E W // q.comp f.1 = Q} ≃ QuadraticRealizations Q q where
  toFun f := ⟨f.1.1, f.1.2, f.2⟩
  invFun f := ⟨⟨f.1, f.2.1⟩, f.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [FiniteDimensional (ZMod 2) E] [∀ i, FiniteDimensional (ZMod 2) (V i)] in
/-- The free coordinates are counted as actual maps. The pivot cost is paid
once for each independent retained relation, jointly. -/
theorem quadraticRelationTuples_count_le
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (P : CoordinatePivotSystem (quadraticRelationCoordinate B))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (M : ℕ) (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ M) :
    Nat.card (QuadraticRelationTuples (E := E) B q) ≤
      (∏ i : {i : ι // i ∉ P.indices}, Nat.card (SurjectiveBinaryMaps E (V i.1))) *
        M ^ Module.finrank (ZMod 2) B := by
  letI : ∀ i, Finite (E →ₗ[ZMod 2] V i) := fun _ =>
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI : ∀ i, Fintype (SurjectiveBinaryMaps E (V i)) := fun _ => Fintype.ofFinite _
  apply P.solution_count_le (A := fun i => SurjectiveBinaryMaps E (V i))
    (fun i f => (q i).comp f.1) M
  intro i Q
  rw [Nat.card_congr (quadraticOutcomeFibreEquiv (q i) Q)]
  exact (quadraticRealization_card_le Q (q i) (hq i)).trans (hM i)

/-- A surjection count is bounded by the exact count of all linear maps. -/
theorem surjectiveBinaryMaps_count_le {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Finite W] :
    Nat.card (SurjectiveBinaryMaps E W) ≤
      2 ^ (Module.finrank (ZMod 2) E * Module.finrank (ZMod 2) W) := by
  letI : Finite (E →ₗ[ZMod 2] W) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  calc
    _ ≤ Nat.card (E →ₗ[ZMod 2] W) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = _ := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap]; simp

/-- Dimension form of the joint incidence bound, retaining exactly the
nonpivot factors and the actual dimension of the relation space. -/
theorem quadraticRelationTuples_count_le_pow
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (P : CoordinatePivotSystem (quadraticRelationCoordinate B))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (M : ℕ) (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ M) :
    Nat.card (QuadraticRelationTuples (E := E) B q) ≤
      2 ^ (Module.finrank (ZMod 2) E *
        ∑ i : {i : ι // i ∉ P.indices}, Module.finrank (ZMod 2) (V i.1)) *
      M ^ Module.finrank (ZMod 2) B := by
  apply (quadraticRelationTuples_count_le B P q hq M hM).trans
  apply Nat.mul_le_mul_right
  calc
    _ ≤ ∏ i : {i : ι // i ∉ P.indices},
        2 ^ (Module.finrank (ZMod 2) E * Module.finrank (ZMod 2) (V i.1)) :=
      Finset.prod_le_prod' (fun _ _ => surjectiveBinaryMaps_count_le)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, Finset.mul_sum]

section TotalMaps

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [Finite W]

/-- A literal coordinate map of a linear map into the full product. -/
def quadraticCoordinateMap (f : E →ₗ[ZMod 2] (W × ∀ i, V i)) (i : ι) :
    E →ₗ[ZMod 2] V i :=
  (LinearMap.proj i).comp ((LinearMap.snd (ZMod 2) W (∀ i, V i)).comp f)

/-- Actual linear maps into the full target, surjective on every quadratic
factor and satisfying every retained relation pointwise. No injectivity or
surjectivity onto the free summand is imposed in this upper-counting type. -/
abbrev QuadraticRelationMaps (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) :=
  {f : E →ₗ[ZMod 2] (W × ∀ i, V i) //
    (∀ i, Function.Surjective (fun x => (f x).2 i)) ∧
    ∀ b : B, ∀ x : E, ∑ i, b.1 i * q i ((f x).2 i) = 0}

private def quadraticRelationMapEncode
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (f : QuadraticRelationMaps (E := E) (W := W) B q) :
    (E →ₗ[ZMod 2] W) × QuadraticRelationTuples (E := E) B q :=
  ⟨(LinearMap.fst (ZMod 2) W (∀ i, V i)).comp f.1,
    ⟨fun i => ⟨quadraticCoordinateMap f.1 i, f.2.1 i⟩, by
      intro b
      ext x
      simpa [quadraticCoordinateMap, smul_eq_mul] using f.2.2 b x⟩⟩

omit [FiniteDimensional (ZMod 2) E] [Finite E]
  [∀ i, FiniteDimensional (ZMod 2) (V i)] [∀ i, Finite (V i)]
  [FiniteDimensional (ZMod 2) W] [Finite W] in
private theorem quadraticRelationMapEncode_injective
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) :
    Function.Injective (quadraticRelationMapEncode (E := E) (W := W) B q) := by
  intro f g h
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun z => z.1 x) h
  · funext i
    exact congrArg (fun z => (z.2.1 i).1 x) h

/-- The full target contributes its free linear-map count and the joint
quadratic tuple count, retaining the chosen pivots exactly. -/
theorem quadraticRelationMaps_count_le_pivots
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (P : CoordinatePivotSystem (quadraticRelationCoordinate B))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (M : ℕ) (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ M) :
    Nat.card (QuadraticRelationMaps (E := E) (W := W) B q) ≤
      M ^ Module.finrank (ZMod 2) B *
      2 ^ (Module.finrank (ZMod 2) E * (Module.finrank (ZMod 2) W +
        ∑ i : {i : ι // i ∉ P.indices}, Module.finrank (ZMod 2) (V i.1))) := by
  letI : ∀ i, Finite (E →ₗ[ZMod 2] V i) := fun _ =>
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI : Finite (E →ₗ[ZMod 2] W) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  calc
    _ ≤ Nat.card ((E →ₗ[ZMod 2] W) × QuadraticRelationTuples (E := E) B q) :=
      Nat.card_le_card_of_injective (quadraticRelationMapEncode B q)
        (quadraticRelationMapEncode_injective B q)
    _ = Nat.card (E →ₗ[ZMod 2] W) * Nat.card (QuadraticRelationTuples (E := E) B q) :=
      Nat.card_prod _ _
    _ = 2 ^ (Module.finrank (ZMod 2) E * Module.finrank (ZMod 2) W) *
        Nat.card (QuadraticRelationTuples (E := E) B q) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap]
      rw [show Nat.card (ZMod 2) = 2 by simp]
    _ ≤ 2 ^ (Module.finrank (ZMod 2) E * Module.finrank (ZMod 2) W) *
        (2 ^ (Module.finrank (ZMod 2) E *
          ∑ i : {i : ι // i ∉ P.indices}, Module.finrank (ZMod 2) (V i.1)) *
          M ^ Module.finrank (ZMod 2) B) :=
      Nat.mul_le_mul_left _ (quadraticRelationTuples_count_le_pow B P q hq M hM)
    _ = _ := by rw [Nat.mul_add, pow_add]; ring

/-- Every pivot has dimension at least two; the total dimension therefore
loses at least twice the dimension of the actual retained relation space. -/
theorem quadraticRelationMaps_count_le
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (hdim : ∀ i, 2 ≤ Module.finrank (ZMod 2) (V i))
    (M : ℕ) (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ M) :
    Nat.card (QuadraticRelationMaps (E := E) (W := W) B q) ≤
      M ^ Module.finrank (ZMod 2) B *
      2 ^ (Module.finrank (ZMod 2) E * (Module.finrank (ZMod 2) W +
        ∑ i, Module.finrank (ZMod 2) (V i) - 2 * Module.finrank (ZMod 2) B)) := by
  let P := quadraticRelationPivots B
  have hp : 2 * Module.finrank (ZMod 2) B ≤
      ∑ i : P.indices, Module.finrank (ZMod 2) (V i.1) := by
    calc
      _ = ∑ _i : P.indices, 2 := by simp [P.card_indices, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hdim i.1)
  have hsplit : (∑ i : P.indices, Module.finrank (ZMod 2) (V i.1)) +
      (∑ i : {i : ι // i ∉ P.indices}, Module.finrank (ZMod 2) (V i.1)) =
      ∑ i, Module.finrank (ZMod 2) (V i) := by
    exact Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ P.indices)
      (fun i => Module.finrank (ZMod 2) (V i))
  apply (quadraticRelationMaps_count_le_pivots (W := W) B P q hq M hM).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
  apply Nat.mul_le_mul_left
  omega

end TotalMaps

end SymmetricSubgroupAsymptotics
