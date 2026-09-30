import SymmetricSubgroupAsymptotics.FusionCarrierIncidence

/-!
# Weighted retained-cell incidence for reversible fusion carriers

The uniform retained-cell theorem charges every flag by the same worst-case
Yoneda fibre bound.  That is adequate when all flags have the same residual
capacity, but it loses the correlation between a chosen top and the size of
the fibre below that top.

This file keeps that correlation.  A finite retained flag `a` is assigned its
own cost `L a`; the total incidence capacity is the single sum
`\sum a, L a`.  In particular, no maximum over tops is taken before the
complete quotient moment is invoked.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics

attribute [local instance] Fintype.ofFinite

/-- Finite fibre counting with a cost depending on the second coordinate.
The cost is summed before the cardinality of the first coordinate is paid. -/
theorem natCard_le_fibreCostSum_mul
    {X Y A : Type*} [Finite X] [Finite Y] [Finite A]
    (f : X → Y × A) (L : A → ℕ)
    (hfibre : ∀ (y : Y) (a : A),
      Nat.card {x : X // f x = (y, a)} ≤ L a) :
    Nat.card X ≤ (∑ a : A, L a) * Nat.card Y := by
  calc
    Nat.card X = Nat.card (Σ z : Y × A, {x : X // f x = z}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ z : Y × A, Nat.card {x : X // f x = z} := Nat.card_sigma
    _ ≤ ∑ z : Y × A, L z.2 :=
      Finset.sum_le_sum (fun z _ ↦ hfibre z.1 z.2)
    _ = ∑ y : Y, ∑ a : A, L a := by
      rw [Fintype.sum_prod_type]
    _ = (∑ a : A, L a) * Nat.card Y := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      exact Nat.mul_comm _ _

/-- Weighted retained-cell incidence.  For a fixed complete quotient map and
flag `a`, the fibre may have its own bound `L a`.  The conclusion charges the
joint sum of these bounds, preserving top/fibre correlation. -/
theorem fusionCarrierAcceptedEpi_card_le_of_weightedRetainedCells
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop)
    {R A : Type*} [Group R] [Finite R] [Finite A]
    (cell : FusionCarrierAcceptedEpi C J Accepted →
      CompleteQuotientMap J R × A)
    (L : A → ℕ)
    (hcell : ∀ (d : CompleteQuotientMap J R) (a : A),
      Nat.card {δ : FusionCarrierAcceptedEpi C J Accepted //
        cell δ = (d, a)} ≤ L a) :
    (Nat.card (FusionCarrierAcceptedEpi C J Accepted) : ℝ) ≤
      ((∑ a : A, L a : ℕ) : ℝ) *
        completeQuotientWeight (R := R) J := by
  have hnat := natCard_le_fibreCostSum_mul cell L hcell
  rw [completeQuotientMap_card] at hnat
  unfold completeQuotientWeight
  exact_mod_cast hnat

/-- Numerical capacity form of weighted retained-cell incidence.  The single
capacity inequality is imposed after summing the top-dependent fibre costs. -/
theorem fusionCarrierAcceptedEpi_card_le_ownerCapacity_of_weightedRetainedCells
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop)
    {R A : Type*} [Group R] [Finite R] [Finite A]
    (cell : FusionCarrierAcceptedEpi C J Accepted →
      CompleteQuotientMap J R × A)
    (L : A → ℕ)
    (hcell : ∀ (d : CompleteQuotientMap J R) (a : A),
      Nat.card {δ : FusionCarrierAcceptedEpi C J Accepted //
        cell δ = (d, a)} ≤ L a)
    (D eta : ℝ)
    (hcapacity : ((∑ a : A, L a : ℕ) : ℝ) ≤
      D * (2 : ℝ) ^ (eta * b)) :
    (Nat.card (FusionCarrierAcceptedEpi C J Accepted) : ℝ) ≤
      (D * (2 : ℝ) ^ (eta * b)) *
        completeQuotientWeight (R := R) J := by
  exact (fusionCarrierAcceptedEpi_card_le_of_weightedRetainedCells
    C J Accepted cell L hcell).trans
      (mul_le_mul_of_nonneg_right hcapacity
        (completeQuotientWeight_nonneg (R := R) J))

namespace FusionAxisCarrier

/-- Weighted retained-cell incidence transported through a reversible carrier
to the original action and its literal normal axis. -/
theorem survivingEpiCount_le_of_weightedRetainedCells
    {w b : ℕ}
    {U : Subgroup (Equiv.Perm (Fin w))}
    {P : Subgroup (U × Equiv.Perm (Fin b)) → Prop}
    {N : {N : Subgroup U // N.Normal}}
    (K : FusionAxisCarrier U N)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (K.checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (haccept : ∀ δ : GroupEpimorphism J K.checked.quotient,
      K.checked.carrierInverseSurvival K.source_eq P
          (fusionQuotientGraph K.checked.beta J δ.1) →
        Accepted (fusionQuotientGraph K.checked.beta J δ.1))
    {R A : Type*} [Group R] [Finite R] [Finite A]
    (cell : FusionCarrierAcceptedEpi K.checked J Accepted →
      CompleteQuotientMap J R × A)
    (L : A → ℕ)
    (hcell : ∀ (d : CompleteQuotientMap J R) (a : A),
      Nat.card {δ : FusionCarrierAcceptedEpi K.checked J Accepted //
        cell δ = (d, a)} ≤ L a)
    (D eta : ℝ)
    (hcapacity : ((∑ a : A, L a : ℕ) : ℝ) ≤
      D * (2 : ℝ) ^ (eta * b)) :
    fusionSurvivingEpiCount U P N J ≤
      (D * (2 : ℝ) ^ (eta * b)) *
        completeQuotientWeight (R := R) J := by
  apply K.survivingEpiCount_le_of_intrinsic J Accepted haccept
  exact fusionCarrierAcceptedEpi_card_le_ownerCapacity_of_weightedRetainedCells
    K.checked J Accepted cell L hcell D eta hcapacity

end FusionAxisCarrier

end SymmetricSubgroupAsymptotics

end
