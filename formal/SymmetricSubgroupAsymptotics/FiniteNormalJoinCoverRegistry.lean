import SymmetricSubgroupAsymptotics.FiniteConjugacyCover
import SymmetricSubgroupAsymptotics.FiniteNormalJoinTwoGenerators

/-!
# Normal registries from original-group conjugacy coverage

Normal-state completeness needs coverage by the selected representatives, but
neither separation of those representatives nor exact conjugacy-class sizes.
Here coverage comes from a genuine `FiniteConjugacyCover`: its complete row map
and every conjugator lie in the same original group. The normal states and join
transitions are retained verbatim. No literal cover is constructed in this file.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace FiniteConjugacyCover

/-- The checked original-row conjugators cover every original element. Labels
may repeat and representatives need not be pairwise nonconjugate. -/
theorem covers {G : Type*} [Group G] {n c : ℕ} {rows : Fin n → G}
    (C : FiniteConjugacyCover rows c) (x : G) :
    ∃ j : Fin c, IsConj x (rows (C.representative j)) := by
  obtain ⟨i, rfl⟩ := C.complete x
  exact ⟨C.label i, C.row_isConj i⟩

end FiniteConjugacyCover

/-- The same normal-state and transition data as `FiniteNormalJoinRegistry`,
with the actual row/conjugator cover supplying the required coverage. -/
structure FiniteNormalJoinCoverRegistry
    {G I : Type*} [Group G] {n c : ℕ} {rows : Fin n → G}
    (C : FiniteConjugacyCover rows c) (states : I → Subgroup G) where
  normal : ∀ i, (states i).Normal
  bottom : I
  bottom_eq : states bottom = ⊥
  child : I → Fin c → I
  child_eq : ∀ i j, states (child i j) =
    states i ⊔ Subgroup.normalClosure ({rows (C.representative j)} : Set G)

namespace FiniteNormalJoinCoverRegistry

/-- Coverage and checked joins recover every original normal subgroup.
Finiteness follows from the cover's surjective finite row map. -/
theorem complete {G I : Type*} [Group G] {n c : ℕ} {rows : Fin n → G}
    {C : FiniteConjugacyCover rows c} {states : I → Subgroup G}
    (R : FiniteNormalJoinCoverRegistry C states)
    (N : Subgroup G) [N.Normal] : ∃ i, states i = N := by
  classical
  letI : Finite G := Finite.of_surjective rows C.complete
  letI : Finite N := Finite.of_injective (fun x : N => (x : G))
    Subtype.val_injective
  letI : Fintype N := Fintype.ofFinite N
  have extend : ∀ s : Finset N, ∃ i, states i ≤ N ∧
      ∀ x ∈ s, (x : G) ∈ states i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨R.bottom, ?_, by simp⟩
        rw [R.bottom_eq]
        exact bot_le
    | @insert x s hx ih =>
        obtain ⟨i, hi, hs⟩ := ih
        letI : (states i).Normal := R.normal i
        obtain ⟨j, hxj⟩ := C.covers (x : G)
        have hjN : rows (C.representative j) ∈ N := by
          obtain ⟨g, hg⟩ := isConj_iff.mp hxj
          rw [← hg]
          exact Subgroup.Normal.conj_mem (H := N) inferInstance
            (x : G) x.property g
        refine ⟨R.child i j, ?_, ?_⟩
        · rw [R.child_eq]
          exact sup_le hi (Subgroup.normalClosure_le_normal (by
            intro y hy
            have heq : y = rows (C.representative j) := Set.mem_singleton_iff.mp hy
            exact heq ▸ hjN))
        · intro y hy
          rw [R.child_eq]
          rcases Finset.mem_insert.mp hy with rfl | hy
          · have hj : rows (C.representative j) ∈
                Subgroup.normalClosure ({rows (C.representative j)} : Set G) :=
              Subgroup.subset_normalClosure (by simp)
            have hrep : rows (C.representative j) ∈
                states i ⊔ Subgroup.normalClosure
                  ({rows (C.representative j)} : Set G) :=
              (show Subgroup.normalClosure ({rows (C.representative j)} : Set G) ≤
                  states i ⊔ Subgroup.normalClosure
                    ({rows (C.representative j)} : Set G) from le_sup_right) hj
            letI : (states i ⊔ Subgroup.normalClosure
                ({rows (C.representative j)} : Set G)).Normal := inferInstance
            obtain ⟨g, hg⟩ := isConj_iff.mp hxj.symm
            have hconj : g * rows (C.representative j) * g⁻¹ ∈
                states i ⊔ Subgroup.normalClosure
                  ({rows (C.representative j)} : Set G) :=
              Subgroup.Normal.conj_mem
                (H := states i ⊔ Subgroup.normalClosure
                  ({rows (C.representative j)} : Set G))
                inferInstance (rows (C.representative j)) hrep g
            exact hg ▸ hconj
          · exact (show states i ≤
                states i ⊔ Subgroup.normalClosure
                  ({rows (C.representative j)} : Set G) from le_sup_left) (hs y hy)
  obtain ⟨i, hi, hs⟩ := extend Finset.univ
  exact ⟨i, le_antisymm hi (by
    intro x hx
    exact hs ⟨x, hx⟩ (Finset.mem_univ _))⟩

/-- Two checked joins from the original bottom state give two ambient normal
generators for every original normal subgroup. -/
theorem normal_generating_pair
    {G I : Type} [Group G] {n c : ℕ} {rows : Fin n → G}
    {C : FiniteConjugacyCover rows c} {states : I → Subgroup G}
    (R : FiniteNormalJoinCoverRegistry C states)
    (hreach : ∀ i, ∃ a b, R.child (R.child R.bottom a) b = i)
    (N : Subgroup G) [N.Normal] :
    ∃ x : Fin 2 → G, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨i, rfl⟩ := R.complete N
  obtain ⟨a, b, hab⟩ := hreach i
  refine ⟨![rows (C.representative a), rows (C.representative b)], ?_⟩
  calc
    Subgroup.normalClosure (Set.range
        ![rows (C.representative a), rows (C.representative b)]) =
        Subgroup.normalClosure ({rows (C.representative a)} : Set G) ⊔
          Subgroup.normalClosure ({rows (C.representative b)} : Set G) :=
      normalClosure_pair_tuple _ _
    _ = states (R.child (R.child R.bottom a) b) := by
      rw [R.child_eq, R.child_eq, R.bottom_eq, bot_sup_eq]
    _ = states i := congrArg states hab

/-- The conclusion concerns the quotient by the supplied original normal
subgroup, with no change of group, kernel, or quotient map. -/
theorem quotientSocle_two
    {G I : Type} [Group G] {n c : ℕ} {rows : Fin n → G}
    {C : FiniteConjugacyCover rows c} {states : I → Subgroup G}
    (R : FiniteNormalJoinCoverRegistry C states)
    (hreach : ∀ i, ∃ a b, R.child (R.child R.bottom a) b = i)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 := by
  apply quotientSocleNormalGeneratorBound_of_normal_generating_tuples _ N
  intro M hM
  letI := hM
  exact R.normal_generating_pair hreach M

end FiniteNormalJoinCoverRegistry
end SymmetricSubgroupAsymptotics

end
