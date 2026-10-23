import SymmetricSubgroupAsymptotics.FiniteConjugacyCover
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.Fin.VecNotation

/-! Sparse conjugacy covers in the literal A4 and S4 groups. All
representatives AND all conjugators belong to the same original group.
The two bounded kernel-checked statements range over twelve and twenty
four original elements, not over a subgroup powerset or a catalogue. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.FourPointClassRepresentativeCovers

theorem class_card_le_of_representatives {G : Type*} [Group G] (c : ℕ)
    (representatives : Fin c → G)
    (hcover : ∀ g : G, ∃ i : Fin c, ∃ a : G,
      a*g = representatives i*a) : Nat.card (ConjClasses G) ≤ c := by
  have hsurj : Function.Surjective (fun i : Fin c => ConjClasses.mk (representatives i)) := by
    intro q
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep q
    obtain ⟨i, a, ha⟩ := hcover g
    refine ⟨i, ?_⟩
    exact (ConjClasses.mk_eq_mk_iff_isConj.mpr
      (isConj_iff.mpr ⟨a, mul_inv_eq_iff_eq_mul.mpr ha⟩)).symm
  simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective _ hsurj

private def symmetricRepresentatives : Fin 5 → Equiv.Perm (Fin 4) :=
  ![1, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3]

private def alternatingRepresentatives : Fin 4 → alternatingGroup (Fin 4) :=
  ![1, ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      change Equiv.Perm.sign (Equiv.swap 0 1 * Equiv.swap 2 3) = 1
      decide +kernel⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
      change Equiv.Perm.sign (Equiv.swap 0 1 * Equiv.swap 1 2) = 1
      decide +kernel⟩,
    ⟨(Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹, by
      change Equiv.Perm.sign ((Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹) = 1
      decide +kernel⟩]

private theorem symmetric_cover : ∀ g : Equiv.Perm (Fin 4),
    ∃ i : Fin 5, ∃ a : Equiv.Perm (Fin 4),
      a*g = symmetricRepresentatives i*a := by decide +kernel

private theorem alternating_cover : ∀ g : alternatingGroup (Fin 4),
    ∃ i : Fin 4, ∃ a : alternatingGroup (Fin 4),
      a*g = alternatingRepresentatives i*a := by decide +kernel

theorem symmetric_class_card_le_five :
    Nat.card (ConjClasses (Equiv.Perm (Fin 4))) ≤ 5 :=
  class_card_le_of_representatives 5 symmetricRepresentatives symmetric_cover

theorem alternating_class_card_le_four :
    Nat.card (ConjClasses (alternatingGroup (Fin 4))) ≤ 4 :=
  class_card_le_of_representatives 4 alternatingRepresentatives alternating_cover

end SymmetricSubgroupAsymptotics.FourPointClassRepresentativeCovers
