import SymmetricSubgroupAsymptotics.ActualWreathSemisimpleCoefficient
import SymmetricSubgroupAsymptotics.LinearThreeSolvable
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Data.Nat.Log

/-!
Two-generation implies the faithful-simple logarithmic generator bound.
The small-degree obstruction is elementary: a faithful action on fewer
than four points embeds the group in the soluble symmetric group S₄.
A soluble simple group is commutative, which contradicts centerlessness.
The finite-simple two-generation input remains a published assumption.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The faithful-simple generator input is redundant when the finite-simple
two-generation theorem is already retained. -/
theorem FiniteSimpleTwoGeneratorBound.faithfulSimplePermutationGeneratorBound
    (hgen : FiniteSimpleTwoGeneratorBound) :
    FaithfulSimplePermutationGeneratorBound := by
  intro w G _ _ hsimple hcenter rho hrho
  letI : IsSimpleGroup G := hsimple
  have hw : 4 ≤ w := by
    by_contra hn
    have hcard : Fintype.card (Fin w) ≤ Fintype.card (Fin 4) := by
      simp only [Fintype.card_fin]
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    letI : IsSolvable (Equiv.Perm (Fin 4)) := naturalS4_isSolvable
    letI : IsSolvable (Equiv.Perm (Fin w)) :=
      solvable_of_solvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
    have hsol : IsSolvable G := solvable_of_solvable_injective hrho
    have hcomm : ∀ a b : G, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr hsol
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    exact hg (hcenter g (hcomm g))
  have hlog : 2 ≤ Nat.log2 w := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega)).2
      (by norm_num; omega)
  obtain ⟨S, hS, hScard⟩ := hgen G hsimple hcenter
  exact ⟨S, hS, hScard.trans hlog⟩

end SymmetricSubgroupAsymptotics
