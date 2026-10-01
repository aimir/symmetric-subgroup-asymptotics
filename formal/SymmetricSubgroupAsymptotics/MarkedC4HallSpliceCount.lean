import SymmetricSubgroupAsymptotics.MarkedC4CaseISplice
import SymmetricSubgroupAsymptotics.MarkedC4HallCount
import SymmetricSubgroupAsymptotics.AbelianProductGraphClassification

/-!
# Exact Hall fibres with literal cyclic-four coordinates

The existing quotient-graph classification identifies the subgroups over one
fixed source `E` with the disjoint union of literal kernels `K ≤ T` and maps
`E → T/K`.  This file combines that exact identity with the complete Hall
count and the proved columns of `A × C₄^r`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

universe u

/-- The auxiliary cyclic-four coordinate group has exponent dividing `2^N`
as soon as `N ≥ 2`. -/
theorem hasExp2_cyclicFourCoordinates (r N : ℕ) (hN : 2 ≤ N) :
    HasExp2 (Multiplicative (Fin r → ZMod 4)) N := by
  intro x
  apply Multiplicative.toAdd.injective
  funext i
  change (2 ^ N : ℕ) • x.toAdd i = 0
  rw [nsmul_eq_mul]
  have hd : 4 ∣ 2 ^ N := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [pow_add]
    norm_num
  have hc : ((2 ^ N : ℕ) : ZMod 4) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 4) 4 (2 ^ N)).2 hd
  rw [hc, zero_mul]

/-- Exponent bounds are preserved after adjoining literal cyclic-four
coordinates. -/
theorem hasExp2_prod_cyclicFourCoordinates
    (A : Type u) [CommGroup A] (N r : ℕ)
    (hA : HasExp2 A N) (hN : 2 ≤ N) :
    HasExp2 (A × Multiplicative (Fin r → ZMod 4)) N := by
  intro x
  apply Prod.ext
  · exact hA x.1
  · exact hasExp2_cyclicFourCoordinates r N hN x.2

/-- The exact cardinality of a fixed second-full Hall fibre. -/
theorem card_fullSecond_eq_sum_hom
    (T : Type u) [CommGroup T] [Finite T] [Fintype (Subgroup T)]
    (E : Type u) [Group E] [Finite E] :
    Nat.card (AbelianProductGraphClassification.FullSecond T E) =
      ∑ K : Subgroup T, Nat.card (E →* T ⧸ K) := by
  letI (K : Subgroup T) : Finite (T ⧸ K) :=
    Finite.of_surjective (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective _)
  letI (K : Subgroup T) : Finite (E →* T ⧸ K) :=
    Finite.of_injective (fun f : E →* T ⧸ K => (f : E → T ⧸ K))
      DFunLike.coe_injective
  rw [Nat.card_congr
    (AbelianProductGraphClassification.fullClassification (E := T) (B := E)),
    Nat.card_sigma]

/-- Complete Hall bound after adjoining `r` literal `C₄` coordinates.  The
first two target columns are exactly `col A k + r`; every later target column
is unchanged. -/
theorem cyclicFourHallFibre_le
    (N r : ℕ) (A : Type u) [CommGroup A] [Finite A]
    [Fintype (Subgroup (A × Multiplicative (Fin r → ZMod 4)))]
    (hA : HasExp2 A N) (hN : 2 ≤ N)
    (E : Type u) [Group E] [Finite E] :
    ((∑ K : Subgroup (A × Multiplicative (Fin r → ZMod 4)),
        Nat.card (E →* (A × Multiplicative (Fin r → ZMod 4)) ⧸ K) : ℕ) : ℝ)
    ≤ (∏ k ∈ Finset.range N,
          (((col (A × Multiplicative (Fin r → ZMod 4)) k : ℕ) : ℝ) + 1)) * 4 ^ N *
        (2 : ℝ) ^ (∑ k ∈ Finset.range N,
          psi (col (A × Multiplicative (Fin r → ZMod 4)) k)
            (col (Abelianization E) k)) := by
  have hT := sum_card_hom_quotient_le N
    (A × Multiplicative (Fin r → ZMod 4))
    (hasExp2_prod_cyclicFourCoordinates A N r hA hN) E
  exact hT

/-- The same bound stated directly for the exact second-full subgroup
family. -/
theorem cyclicFourFullSecond_le
    (N r : ℕ) (A : Type u) [CommGroup A] [Finite A]
    [Fintype (Subgroup (A × Multiplicative (Fin r → ZMod 4)))]
    (hA : HasExp2 A N) (hN : 2 ≤ N)
    (E : Type u) [Group E] [Finite E] :
    (Nat.card (AbelianProductGraphClassification.FullSecond
      (A × Multiplicative (Fin r → ZMod 4)) E) : ℝ)
    ≤ (∏ k ∈ Finset.range N,
          (((col (A × Multiplicative (Fin r → ZMod 4)) k : ℕ) : ℝ) + 1)) * 4 ^ N *
        (2 : ℝ) ^ (∑ k ∈ Finset.range N,
          psi (col (A × Multiplicative (Fin r → ZMod 4)) k)
            (col (Abelianization E) k)) := by
  rw [card_fullSecond_eq_sum_hom]
  exact cyclicFourHallFibre_le N r A hA hN E

end MarkedC4
end SymmetricSubgroupAsymptotics

end
