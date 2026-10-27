import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators

/-! Literal labelled subgroup counting by bounded ordinary generators.
The small-order consequence is useful only when its binary order exponent
is itself sufficiently small; it is not an LMM transitive count theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteSubgroupSmallOrderCount

variable {G : Type} [Group G] [Finite G]

theorem exists_ambient_tuple (H : Subgroup G) (k : ℕ)
    (hk : MarkedC4.genRank H ≤ k) :
    ∃ f : Fin k → G, Subgroup.closure (Set.range f)=H := by
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := H)
  let eS := Fintype.equivFin S
  let f : Fin k → H := fun j =>
    if h : j.val < Fintype.card S then (eS.symm ⟨j.val,h⟩ : S) else 1
  have hf : Subgroup.closure (Set.range f)=⊤ := by
    apply top_unique
    rw [←hgen]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    let z := eS ⟨x,hx⟩
    have hSk : Fintype.card S ≤ k := by simpa only [Fintype.card_coe,hcard] using hk
    let j : Fin k := ⟨z.val,lt_of_lt_of_le z.isLt hSk⟩
    apply Subgroup.subset_closure
    refine ⟨j,?_⟩
    dsimp [f,j]
    rw [if_pos z.isLt]
    exact congrArg (fun a : S => (a : H)) (eS.symm_apply_apply ⟨x,hx⟩)
  refine ⟨fun i => (f i : G),?_⟩
  have hm := congrArg (Subgroup.map H.subtype) hf
  rw [MonoidHom.map_closure,←Set.range_comp'] at hm
  rw [←MonoidHom.range_eq_map,Subgroup.range_subtype] at hm
  exact hm

theorem card_rank_bounded_subgroups_le (k : ℕ) :
    Nat.card {H : Subgroup G // MarkedC4.genRank H ≤ k} ≤ (Nat.card G)^k := by
  let encode : {H : Subgroup G // MarkedC4.genRank H ≤ k} → (Fin k → G) :=
    fun H => Classical.choose (exists_ambient_tuple H.val k H.property)
  have hencode (H : {H : Subgroup G // MarkedC4.genRank H ≤ k}) :
      Subgroup.closure (Set.range (encode H))=H.val :=
    Classical.choose_spec (exists_ambient_tuple H.val k H.property)
  have hinj : Function.Injective encode := by
    intro H K h
    apply Subtype.ext
    rw [←hencode H,←hencode K,h]
  have hh := Nat.card_le_card_of_injective encode hinj
  simpa only [Nat.card_fun,Nat.card_fin] using hh

theorem card_small_order_subgroups_le (k : ℕ) :
    Nat.card {H : Subgroup G // Nat.card H ≤ 2^k} ≤ (Nat.card G)^k := by
  let f : {H : Subgroup G // Nat.card H ≤ 2^k} →
      {H : Subgroup G // MarkedC4.genRank H ≤ k} := fun H =>
    ⟨H.val,FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow H.val k H.property⟩
  have hf : Function.Injective f := by
    intro H K h
    exact Subtype.ext (congrArg (fun a : {U : Subgroup G // MarkedC4.genRank U ≤ k} => a.val) h)
  exact (Nat.card_le_card_of_injective f hf).trans (card_rank_bounded_subgroups_le k)

/-- Any literal predicate may be imposed without increasing this count. -/
theorem card_small_order_filtered_subgroups_le (k : ℕ) (P : Subgroup G → Prop) :
    Nat.card {H : Subgroup G // P H ∧ Nat.card H ≤ 2^k} ≤ (Nat.card G)^k := by
  let f : {H : Subgroup G // P H ∧ Nat.card H ≤ 2^k} →
      {H : Subgroup G // Nat.card H ≤ 2^k} := fun H => ⟨H.val,H.property.2⟩
  have hf : Function.Injective f := by
    intro H K h
    exact Subtype.ext (congrArg (fun a : {U : Subgroup G // Nat.card U ≤ 2^k} => a.val) h)
  exact (Nat.card_le_card_of_injective f hf).trans (card_small_order_subgroups_le k)

end SymmetricSubgroupAsymptotics.FiniteSubgroupSmallOrderCount
