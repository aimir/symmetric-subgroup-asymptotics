import SymmetricSubgroupAsymptotics.AllLifts

/-!
# Exact noncanonical fixed-image lift counts

The canonical full preimage is the unique lift containing the whole kernel.
Removing this actual subgroup agrees exactly with removing the zero
annihilator term, before any exceptional-incidence estimate is applied.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {G K V : Type*} [Group G] [AddCommGroup K] [Module (ZMod 2) K]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- A lift contains the complete kernel exactly when it is the full
preimage of its specified image. -/
theorem binary_image_lift_canonical_iff (π : G →* Multiplicative V)
    (U : Submodule (ZMod 2) V) (H : Subgroup G)
    (hH : H.map π = U.toAddSubgroup.toSubgroup) :
    π.ker ≤ H ↔ H = U.toAddSubgroup.toSubgroup.comap π := by
  constructor
  · intro hker
    rw [← hH]
    exact (Subgroup.comap_map_eq_self hker).symm
  · rintro rfl
    intro g hg
    change π g ∈ U.toAddSubgroup.toSubgroup
    rw [show π g = 1 from hg]
    exact U.toAddSubgroup.toSubgroup.one_mem

/-- Exactly one actual subgroup over a specified image contains the entire
kernel. Surjectivity supplies that full preimage. -/
theorem binary_image_canonical_lift_count (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (U : Submodule (ZMod 2) V) :
    Nat.card {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup ∧ π.ker ≤ H} = 1 := by
  letI : Unique {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup ∧ π.ker ≤ H} :=
    { default := ⟨U.toAddSubgroup.toSubgroup.comap π,
        Subgroup.map_comap_eq_self_of_surjective hπ _,by
          intro g hg
          change π g ∈ U.toAddSubgroup.toSubgroup
          rw [show π g = 1 from hg]
          exact U.toAddSubgroup.toSubgroup.one_mem⟩
      uniq := fun H ↦ Subtype.ext ((binary_image_lift_canonical_iff π U H.val H.property.1).mp
        H.property.2) }
  exact Nat.card_unique

section FiniteCount

variable [Finite G] [Finite K]

attribute [local instance] Fintype.ofFinite

private instance : Finite (Module.Dual (ZMod 2) K) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) K ↦ (f : K → ZMod 2))
    DFunLike.coe_injective

/-- A disjoint partition of the actual fixed-image fibre into the unique
canonical lift and all noncanonical lifts. -/
theorem binary_image_lifts_count_partition (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (U : Submodule (ZMod 2) V) :
    1 + Nat.card {H : Subgroup G //
      H.map π = U.toAddSubgroup.toSubgroup ∧ ¬ π.ker ≤ H} =
      Nat.card {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup} := by
  let p : Subgroup G → Prop := fun H ↦ H.map π = U.toAddSubgroup.toSubgroup
  let q : Subgroup G → Prop := fun H ↦ π.ker ≤ H
  have h := Nat.card_congr (Equiv.sumCompl (fun H : {H // p H} ↦ q H.val))
  rw [Nat.card_sum,
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p q),
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p (fun H ↦ ¬ q H))] at h
  change Nat.card {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup ∧ π.ker ≤ H} + _ = _ at h
  rw [binary_image_canonical_lift_count π hπ U] at h
  exact h

omit [Finite G] in
/-- The zero annihilator contributes precisely the one canonical lift. -/
theorem binary_annihilator_weight_partition (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (U : Submodule (ZMod 2) V) :
    1 + (∑ B : {B : Submodule (ZMod 2) (binaryImageSquareObstruction π e U).dualAnnihilator // B ≠ ⊥},
      2 ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B.val)) =
      ∑ B : Submodule (ZMod 2) (binaryImageSquareObstruction π e U).dualAnnihilator,
        (2 : ℕ) ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B) := by
  let A := (binaryImageSquareObstruction π e U).dualAnnihilator
  have h := Fintype.sum_subtype_add_sum_subtype (fun B : Submodule (ZMod 2) A ↦ B = ⊥)
    (fun B ↦ (2 : ℕ) ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B))
  simp only [Fintype.sum_unique] at h
  have hb (B : {B : Submodule (ZMod 2) A // B = ⊥}) : Module.finrank (ZMod 2) B.val = 0 := by
    rw [B.property]
    exact finrank_bot _ _
  simpa only [hb,mul_zero,pow_zero] using h

/-- Exact count of actual noncanonical subgroups with a fixed image. The
annihilator is the original retained square-annihilator, and only its zero
subspace is removed. -/
theorem binary_image_noncanonical_lifts_count_annihilator (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (e : Multiplicative K ≃* π.ker)
    (hcentral : π.ker ≤ Subgroup.center G) (U : Submodule (ZMod 2) V) :
    Nat.card {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup ∧ ¬ π.ker ≤ H} =
      ∑ B : {B : Submodule (ZMod 2) (binaryImageSquareObstruction π e U).dualAnnihilator // B ≠ ⊥},
        2 ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B.val) := by
  have h := binary_image_lifts_count_partition π hπ U
  rw [binary_image_lifts_count_annihilator π hπ e hcentral U,
    ← binary_annihilator_weight_partition π e U] at h
  exact Nat.add_left_cancel h

/-- Nonzero subspaces of a retained subspace are exactly the nonzero
ambient subspaces contained in it. The ambient embeddings are preserved. -/
def nonzeroSubspaceBelowEquiv {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (A : Submodule (ZMod 2) E) :
    {B : Submodule (ZMod 2) A // B ≠ ⊥} ≃
      {B : Submodule (ZMod 2) E // B ≤ A ∧ B ≠ ⊥} :=
  (Equiv.subtypeEquiv A.mapIic.toEquiv (fun B ↦ by
    change B ≠ ⊥ ↔ (A.mapIic B).val ≠ ⊥
    constructor
    · intro hB hzero
      apply hB
      apply A.mapIic.injective
      apply Subtype.ext
      simpa only [map_bot] using hzero
    · intro hB hzero
      apply hB
      simp only [hzero,map_bot]
      rfl)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun B : Submodule (ZMod 2) E ↦ B ≤ A)
      (fun B ↦ B ≠ ⊥))

theorem nonzeroSubspaceBelowEquiv_finrank {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (A : Submodule (ZMod 2) E) (B : {B : Submodule (ZMod 2) A // B ≠ ⊥}) :
    Module.finrank (ZMod 2) (nonzeroSubspaceBelowEquiv A B).val =
      Module.finrank (ZMod 2) B.val :=
  Submodule.finrank_map_subtype_eq A B.val

/-- The same exact count with the retained annihilator as a condition on
actual subspaces of the original dual kernel space. -/
theorem binary_image_noncanonical_lifts_count_original_annihilator (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (e : Multiplicative K ≃* π.ker)
    (hcentral : π.ker ≤ Subgroup.center G) (U : Submodule (ZMod 2) V) :
    Nat.card {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup ∧ ¬ π.ker ≤ H} =
      ∑ B : {B : Submodule (ZMod 2) (Module.Dual (ZMod 2) K) //
        B ≤ (binaryImageSquareObstruction π e U).dualAnnihilator ∧ B ≠ ⊥},
        2 ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B.val) := by
  rw [binary_image_noncanonical_lifts_count_annihilator π hπ e hcentral U]
  exact Fintype.sum_equiv (nonzeroSubspaceBelowEquiv (binaryImageSquareObstruction π e U).dualAnnihilator)
    _ _ (fun B ↦ by rw [nonzeroSubspaceBelowEquiv_finrank])

/-- Real-valued form ready for the uniform weighted incidence estimate. -/
theorem binary_image_noncanonical_lifts_count_original_annihilator_real (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (e : Multiplicative K ≃* π.ker)
    (hcentral : π.ker ≤ Subgroup.center G) (U : Submodule (ZMod 2) V) :
    (Nat.card {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup ∧ ¬ π.ker ≤ H} : ℝ) =
      ∑ B : {B : Submodule (ZMod 2) (Module.Dual (ZMod 2) K) //
        B ≤ (binaryImageSquareObstruction π e U).dualAnnihilator ∧ B ≠ ⊥},
        (2 : ℝ) ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B.val) := by
  exact_mod_cast binary_image_noncanonical_lifts_count_original_annihilator π hπ e hcentral U

end FiniteCount

end SymmetricSubgroupAsymptotics
