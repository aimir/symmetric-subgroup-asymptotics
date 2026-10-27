import SymmetricSubgroupAsymptotics.MinimalTransitiveActualFactorThreeDivisor
import SymmetricSubgroupAsymptotics.ActualNormalSimpleProductStabilizerRestriction
import SymmetricSubgroupAsymptotics.CoupledSimpleProductIntersectionStructure

/-! Exact subgroup-classification target on one active factor of the actual
nonabelian minimal normal subgroup. Original action, point, and chart are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MinimalTransitiveActualSimpleIntersectionStructure
open SimpleProductAxisStabilizerRestriction
open ActualNormalSimpleProductStabilizerRestriction
open CoupledSimpleProductIntersectionStructure
variable {G X J T : Type} [Group G] [Finite G] [Finite X]
  [MulAction G X] [MulAction.IsPretransitive G X] [FaithfulSMul G X]
  [Group T] [Finite T] [IsSimpleGroup T] [Fintype J] [DecidableEq J]

theorem exists_actual_simple_intersection
    (hmin : ∀ N : Subgroup G,MulAction.IsPretransitive N X → N=⊤)
    (L : Subgroup G) (hL : IsMinimalNormalSubgroup L)
    (hnL : ¬IsMulCommutative L) (e : L ≃* (J → T))
    (hnT : ¬IsMulCommutative T) (m : ℕ) (hdegree : Nat.card X=3*2^m) (x : X) :
    ∃ i : J,
      let K := (chartStabilizer L e x).comap (axis i)
      let P := (chartStabilizer L e x).map (coordinate i)
      K ≠ ⊥ ∧ K ≠ ⊤ ∧ (∃ a : ℕ,K.index=3*2^a) ∧
        K ≤ P ∧ P ≤ Subgroup.normalizer (K : Set T) := by
  letI : L.Normal := hL.1
  obtain ⟨i,hi⟩ := MinimalTransitiveActualFactorThreeDivisor.exists_actual_factor_three_divisor
    hmin L hL hnL e m hdegree x
  letI : MulAction T X := MulAction.compHom X
    (MinimalTransitiveActualFactorThreeDivisor.axisInclusion L e i)
  have hs : MulAction.stabilizer T x=(chartStabilizer L e x).comap (axis i) := by
    ext t
    constructor
    · intro ht
      change (e.symm (axis i t) : G) • x=x at ht
      exact ⟨e.symm (axis i t),ht,e.apply_symm_apply _⟩
    · rintro ⟨l,hl,he⟩
      have hel : l=e.symm (axis i t) := e.injective (by simpa using he)
      change (e.symm (axis i t) : G) • x=x
      rw [hel] at hl
      exact hl
  change 3 ∣ (MulAction.stabilizer T x).index at hi
  rw [hs] at hi
  refine ⟨i,selected_intersection_structure hnT (chartStabilizer L e x) i m ?_ hi⟩
  exact chart_stabilizer_index_dvd L e x m (by rw [hdegree])

end SymmetricSubgroupAsymptotics.MinimalTransitiveActualSimpleIntersectionStructure
