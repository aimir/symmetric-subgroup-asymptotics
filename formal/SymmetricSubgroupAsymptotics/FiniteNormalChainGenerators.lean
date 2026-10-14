import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finset.Max

/-!
# Every normal subgroup in a finite normal chain is normally cyclic

Among the normal closures of individual elements of a given normal subgroup,
choose one of maximal order. Comparability makes it contain every other such
closure, so it is the entire subgroup. This strengthens a quotient-socle
bound to a uniform bound for all original normal subgroups.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem normal_generating_singletons_of_finite_normal_total
    {G : Type} [Group G] [Finite G]
    (hchain : ∀ K L : Subgroup G, K.Normal → L.Normal → K ≤ L ∨ L ≤ K) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin 1 → G, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  letI : Fintype N := Fintype.ofFinite N
  let C (x : N) : Subgroup G :=
    Subgroup.normalClosure (Set.range (fun _ : Fin 1 ↦ (x : G)))
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image (Finset.univ : Finset N)
    (fun y ↦ Nat.card (C y)) Finset.univ_nonempty
  have hle (y : N) : C y ≤ C x := by
    rcases hchain (C x) (C y) (by dsimp [C]; infer_instance)
        (by dsimp [C]; infer_instance) with h | h
    · exact (Subgroup.eq_of_le_of_card_ge h (hx y (Finset.mem_univ y))).ge
    · exact h
  refine ⟨fun _ ↦ (x : G), le_antisymm ?_ ?_⟩
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact x.2
  · intro y hy
    apply hle ⟨y, hy⟩
    exact Subgroup.subset_normalClosure (Set.mem_range_self (0 : Fin 1))

end SymmetricSubgroupAsymptotics

end
