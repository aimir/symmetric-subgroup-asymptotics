import SymmetricSubgroupAsymptotics.CFSGFFourE6NonAdjacentRoots
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalA2
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMiddleFactors
import Mathlib.Tactic.Group

/-! The unoriented F4 simple path is intrinsic in the positive ORIGINAL
root charts: distinct adjacent charts fail to commute, in every
characteristic, while all nonadjacent charts commute. The middle edge
retains its coefficient-one mixed factor even in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveCommutationPath
open CFSGFFourE6NonAdjacentRoots CFSGFFourE6OriginalA2 CFSGFFourE6OriginalMiddleFactors
open CFSGFFourE6OriginalSimpleParameters CFSGFourRootPathPermutation CFSG.Models.Chevalley

private theorem commutator_one {G : Type*} [Group G] (x y : G) (h : Commute x y) :
    x*y*x⁻¹*y⁻¹ = 1 := by
  rw [h.eq]
  group

private theorem a2_noncommuting {K G : Type*} [Field K] [Group G]
    (w : Multiplicative K →* G) (hinj : Function.Injective w) (x y : G)
    (he : x*y*x⁻¹*y⁻¹ = w (Multiplicative.ofAdd 1)) : ¬ Commute x y := by
  intro hc
  have hz := he.symm.trans (commutator_one x y hc)
  have hp := hinj (hz.trans (map_one w).symm)
  exact (show (1 : K) ≠ 0 from one_ne_zero)
    (congrArg (fun z : Multiplicative K => z.toAdd) hp)

private theorem four_chart_adjacent {G : Type*} [Monoid G] (x : Fin 4 → G)
    (h01 : ¬ Commute (x 0) (x 1)) (h12 : ¬ Commute (x 1) (x 2))
    (h23 : ¬ Commute (x 2) (x 3)) (i j : Fin 4) (h : adjacent i j) :
    ¬ Commute (x i) (x j) := by
  fin_cases i <;> fin_cases j <;> first
    | exact h01
    | exact h12
    | exact h23
    | exact fun hc => h01 hc.symm
    | exact fun hc => h12 hc.symm
    | exact fun hc => h23 hc.symm
    | exact False.elim (by norm_num [adjacent] at h)

theorem original_adjacent_not_commute_one (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (i j : Fin 4) (h : adjacent i j) :
    ¬ Commute (originalSimpleHom K false i (Multiplicative.ofAdd 1))
      (originalSimpleHom K false j (Multiplicative.ofAdd 1)) := by
  apply four_chart_adjacent (fun k => originalSimpleHom K false k (Multiplicative.ofAdd 1))
    ?_ ?_ ?_ i j h
  · apply a2_noncommuting (sumOriginalHom K 0 1) (sumOriginalHom_injective K p 0 1)
    simpa only [one_mul] using original_paired_commutator K 0 1 (by decide) 1 1
  · intro hc
    have hm := original_middle_commutator K 1 1
    have hh : middleLongOriginalHom K (Multiplicative.ofAdd 1)*
        middleShortOriginalHom K (Multiplicative.ofAdd (-1)) = 1 := by
      simpa only [one_mul] using hm.symm.trans
        (commutator_one _ _ hc)
    have hz : middleLongOriginalHom K (Multiplicative.ofAdd 0)*
        middleShortOriginalHom K (Multiplicative.ofAdd 0) = 1 := by
      change middleLongOriginalHom K 1*middleShortOriginalHom K 1 = 1
      rw [map_one, map_one, one_mul]
    exact (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))
      (original_middleFactor_snd_eq K p 1 0 (-1) 0 (hh.trans hz.symm))
  · apply a2_noncommuting (sumOriginalHom K 2 3) (sumOriginalHom_injective K p 2 3)
    simpa only [one_mul] using original_singleton_commutator K 1 0 (by decide) 1 1

theorem original_charts_commute_iff_nonadjacent (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (i j : Fin 4) :
    (∀ a b : Multiplicative K, Commute (originalSimpleHom K false i a)
      (originalSimpleHom K false j b)) ↔ ¬ adjacent i j := by
  constructor
  · intro hc hij
    exact original_adjacent_not_commute_one K p i j hij (hc _ _)
  · intro hij a b
    exact original_nonadjacent_commute K i j hij a b

end SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveCommutationPath
