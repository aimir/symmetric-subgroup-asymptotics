import SymmetricSubgroupAsymptotics.FiniteConjugacyCardinalCover
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Complete normal registries from conjugacy-class joins

A finite witness need not assert that its displayed normal-subgroup list is
complete.  It suffices to prove a sparse conjugacy-class cover, include the
bottom subgroup, and give a checked transition adjoining the normal closure
of each selected class representative.  Finite induction then reconstructs
every literal normal subgroup.

For the six-pair affine catalogue this reduces the largest action from tens
of thousands of point rows to its selected conjugacy classes and at most 44
normal states.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {G I : Type*} [Group G] [Finite G] {c : ℕ}
    {representative : Fin c → G} {states : I → Subgroup G}

/-- A finite state machine closed under adjoining the normal closure of each
selected conjugacy-class representative. -/
structure FiniteNormalJoinRegistry
    (C : FiniteConjugacyCardinalCover representative)
    (states : I → Subgroup G) where
  normal : ∀ i, (states i).Normal
  bottom : I
  bottom_eq : states bottom = ⊥
  child : I → Fin c → I
  child_eq : ∀ i j, states (child i j) =
    states i ⊔ Subgroup.normalClosure ({representative j} : Set G)

namespace FiniteNormalJoinRegistry

variable {C : FiniteConjugacyCardinalCover representative}
    (R : FiniteNormalJoinRegistry C states)

include C R

/-- Every literal normal subgroup is one of the checked states.  Completeness
is proved here and is not an input of the finite certificate. -/
theorem complete (N : Subgroup G) [N.Normal] : ∃ i, states i = N := by
  classical
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
        have hjN : representative j ∈ N :=
          FiniteConjugacyCardinalCover.representative_mem_normal
            (representative := representative) x.property hxj
        refine ⟨R.child i j, ?_, ?_⟩
        · rw [R.child_eq]
          exact sup_le hi (Subgroup.normalClosure_le_normal (by
            intro y hy
            have heq : y = representative j := Set.mem_singleton_iff.mp hy
            exact heq ▸ hjN))
        · intro y hy
          rw [R.child_eq]
          rcases Finset.mem_insert.mp hy with rfl | hy
          · have hj : representative j ∈
                Subgroup.normalClosure ({representative j} : Set G) :=
              Subgroup.subset_normalClosure (by simp)
            have hrep : representative j ∈
                states i ⊔ Subgroup.normalClosure ({representative j} : Set G) :=
              (show Subgroup.normalClosure ({representative j} : Set G) ≤
                  states i ⊔
                    Subgroup.normalClosure ({representative j} : Set G) from
                le_sup_right) hj
            letI : (states i ⊔
                Subgroup.normalClosure ({representative j} : Set G)).Normal :=
              inferInstance
            obtain ⟨g, hg⟩ := isConj_iff.mp hxj.symm
            have hconj : g * representative j * g⁻¹ ∈
                states i ⊔ Subgroup.normalClosure ({representative j} : Set G) :=
              Subgroup.Normal.conj_mem
                (H := states i ⊔
                  Subgroup.normalClosure ({representative j} : Set G))
                inferInstance (representative j) hrep g
            exact hg ▸ hconj
          · exact (show states i ≤
                states i ⊔
                  Subgroup.normalClosure ({representative j} : Set G) from
              le_sup_left) (hs y hy)
  obtain ⟨i, hi, hs⟩ := extend Finset.univ
  exact ⟨i, le_antisymm hi (by
    intro x hx
    exact hs ⟨x, hx⟩ (Finset.mem_univ _))⟩

end FiniteNormalJoinRegistry
end SymmetricSubgroupAsymptotics

end
