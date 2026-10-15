import SymmetricSubgroupAsymptotics.TernaryMovingOrbitCount
import SymmetricSubgroupAsymptotics.EquivariantOrbitFibreCard

/-! One nine-point orbit improves the moving-orbit budget on sixteen
original points from five to three. In an equivariant block map, one
three-point block orbit and one three-point kernel orbit provide the nine
points without choosing or enumerating a subgroup. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.TernaryMovingOrbitCount

variable (P X : Type) [Group P] [MulAction P X] [Finite X]

/-- One large orbit pays its exact excess over the three-point minimum. -/
theorem three_mul_moving_add_six_le (hP : IsPGroup 3 P)
    (q₀ : MulAction.orbitRel.Quotient P X) (hq₀ : 9 ≤ Nat.card q₀.orbit) :
    3 * Nat.card (movingOrbits P X) + 6 ≤ Nat.card X := by
  letI : Fintype (movingOrbits P X) := Fintype.ofFinite _
  let q : movingOrbits P X := ⟨q₀, by omega⟩
  have hsum : 3 * Nat.card (movingOrbits P X) + 6 ≤
      Nat.card (movingPoints P X) := by
    rw [Nat.card_sigma]
    calc
      _ = ∑ o : movingOrbits P X, (3 + if o = q then 6 else 0) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true,
          Nat.card_eq_fintype_card]
        omega
      _ ≤ _ := Finset.sum_le_sum (by
        intro o _
        by_cases ho : o = q
        · subst o
          simpa only [if_true, Nat.reduceAdd] using hq₀
        · simpa only [if_neg ho, Nat.add_zero] using three_le_moving_orbit P X hP o)
  exact hsum.trans (Nat.card_le_card_of_injective
    (movingPoint P X) (movingPoint_injective P X))

/-- No fixed-point premise is needed: the large orbit already pays the
six-point excess needed for this exact sixteen-point budget. -/
theorem moving_le_three_of_large_orbit (hP : IsPGroup 3 P)
    (hX : Nat.card X = 16) (x : X)
    (hx : 9 ≤ Nat.card (MulAction.orbit P x)) :
    Nat.card (movingOrbits P X) ≤ 3 := by
  have h := three_mul_moving_add_six_le P X hP
    (Quotient.mk'' x) hx
  omega

/-- A three-block orbit combined with a nontrivial ternary fibre orbit
supplies the large orbit, using the original equivariant block map. -/
theorem moving_le_three_of_block_and_fibre
    {I : Type} [Finite I] [MulAction P I]
    (b : X → I) (hb : ∀ (g : P) (x : X), b (g • x) = g • b x)
    (K : Subgroup P) (hP : IsPGroup 3 P) (hX : Nat.card X = 16)
    (x : X) (hK : ∀ k : K, (k : P) • b x = b x)
    (hblock : 3 ≤ Nat.card (MulAction.orbit P (b x)))
    (hfibre : 3 ≤ Nat.card (MulAction.orbit K x)) :
    Nat.card (movingOrbits P X) ≤ 3 := by
  apply moving_le_three_of_large_orbit P X hP hX x
  exact (Nat.mul_le_mul hblock hfibre).trans
    (orbit_card_ge_block_mul_fibre b hb K x hK)

end SymmetricSubgroupAsymptotics.TernaryMovingOrbitCount

end
