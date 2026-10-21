import SymmetricSubgroupAsymptotics.CFSGTypeAOrientedCollineation
import SymmetricSubgroupAsymptotics.CFSGProjectiveCollineationCardinality
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearCardComparison
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.Tactic.Ring

/-! The actual outer group of PSL_n(F) has order at most
2*n*|RingAut(F)| for n>=3. Both the geometry and collineation count are
proved on the original matrix quotient; no automorphism lifting or
semilinear-classification premise is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAOuterCardinality
open PrimitiveSocleRawStructure
open CFSGTypeARootGeometryAction CFSGTypeARootActionFaithfulness
variable {F : Type} [Field F] [Finite F] {n : ℕ}
abbrev PSL := Matrix.ProjectiveSpecialLinearGroup (Fin n) F

theorem conj_injective (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3 ≤ n)
    [IsSimpleGroup (PSL (F := F) (n := n))] :
    Function.Injective (MulAut.conj : PSL (F := F) (n := n) →* MulAut (PSL (F := F) (n := n))) := by
  let c := (MulAut.conj : PSL (F := F) (n := n) →* MulAut (PSL (F := F) (n := n)))
  rcases (inferInstance : c.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact c.ker_eq_bot_iff.mp hb
  · obtain ⟨g, hg⟩ := exists_inner_moving_root (F := F) p hn
    have hm : g ∈ c.ker := by rw [ht]; trivial
    have he : c g = 1 := hm
    apply False.elim
    apply hg
    change rootPermutationHom p hn (c g) = 1
    rw [he, map_one]

theorem outer_card_le (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3 ≤ n)
    [IsSimpleGroup (PSL (F := F) (n := n))] :
    Nat.card (Outer (PSL (F := F) (n := n))) ≤ 2 * n * Nat.card (F ≃+* F) := by
  let b : Fin n := ⟨0, by omega⟩
  let i : Fin n := ⟨1, by omega⟩
  let j : Fin n := ⟨2, by omega⟩
  letI : Nonempty (Fin n) := ⟨b⟩
  have hbi : b ≠ i := by intro h; have := congrArg Fin.val h; dsimp [b, i] at this; omega
  have hbj : b ≠ j := by intro h; have := congrArg Fin.val h; dsimp [b, j] at this; omega
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i, j] at this; omega
  have hcol := CFSGProjectiveCollineationCardinality.collineation_card_le_projective_mul_ringAut
    (F := F) b i j hbi hbj hij
  have hpgl := CFSGProjectiveLinearCardComparison.projective_card_le_dimension_mul_specialProjective
    (F := F) (n := Fin n)
  rw [Fintype.card_fin] at hpgl
  have haut : Nat.card (MulAut (PSL (F := F) (n := n))) ≤
      Nat.card (PSL (F := F) (n := n)) * (2 * n * Nat.card (F ≃+* F)) := by
    calc
      Nat.card (MulAut (PSL (F := F) (n := n))) ≤
          2 * Nat.card (CFSGProjectiveFrameCoordinates.collineationGroup (F := F) (n := Fin n)) :=
        CFSGTypeAOrientedCollineation.automorphism_card_le_two_mul_collineation p hn
      _ ≤ 2 * (Nat.card (Matrix.ProjGenLinGroup (Fin n) F) * Nat.card (F ≃+* F)) :=
        Nat.mul_le_mul_left _ hcol
      _ ≤ 2 * ((n * Nat.card (PSL (F := F) (n := n))) * Nat.card (F ≃+* F)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpgl)
      _ = Nat.card (PSL (F := F) (n := n)) * (2 * n * Nat.card (F ≃+* F)) := by ring
  have hinner : Nat.card (Inner (PSL (F := F) (n := n))) = Nat.card (PSL (F := F) (n := n)) :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective p hn)).toEquiv).symm
  have hcard := (Inner (PSL (F := F) (n := n))).card_mul_index
  change Nat.card (Inner (PSL (F := F) (n := n))) * Nat.card (Outer (PSL (F := F) (n := n))) =
    Nat.card (MulAut (PSL (F := F) (n := n))) at hcard
  rw [hinner] at hcard
  have hbound := hcard.trans_le haut
  exact Nat.le_of_mul_le_mul_left hbound (Nat.card_pos (α := PSL (F := F) (n := n)))

end SymmetricSubgroupAsymptotics.CFSGTypeAOuterCardinality
