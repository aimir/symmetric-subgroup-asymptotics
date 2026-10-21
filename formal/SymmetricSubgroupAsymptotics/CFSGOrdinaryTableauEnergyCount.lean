import SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauCount

/-! A local density-energy interface for the exact ordinary tableau
incidence theorem. This keeps exceptional sectors in the SAME table rather
than replacing each normal rank by an unrelated global maximum. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauCount
open MarkedC4 ActualSubdirectFiltration ActualTableauRowIncidence ActualTableauDensityEntropy

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
    (D : ∀ i,Subgroup (F i)) (T : ∀ i j : Fin t,Subgroup (F j))

/-- Only the finite numerical energy of this exact table is abstracted.
The source incidence, diagonal self-cost and multiplicity denominator are
all proved by the actual efficient-array theorem. -/
theorem card_le_of_energy
    (H : TableauFamily F D T) (c n : Fin t → ℝ) (C B E : ℝ)
    (hC : 0 ≤ C)
    (hentry : ∀ i j,j.val ≤ i.val → Real.logb 2 (Nat.card (T i j)) ≤ (C*c i)*n j)
    (hdiag : ∀ i,Real.logb 2 (Nat.card (D i))=(C*c i)*n i)
    (horder : ∀ i,Real.logb 2 (Nat.card (F i)) ≤ B)
    (henergy : (∑ i : Fin t,∑ j : Fin t,
      if j < i then (c i-c j)*n j*(MarkedC4.normalGen (D i) : ℝ) else 0) ≤ E) :
    (Nat.card (TableauFamily F D T) : ℝ) ≤ 
      (2 : ℝ)^(C*E+(t : ℝ)*B^2) := by
  letI (i : Fin t) : (D i).Normal := by
    rw [←H.val.property.2.2 i]
    exact ActualSubdirectFiltration.diagonalNormal F H.val.val H.val.property.1 i
  have hcount := card_le_density_entropy F D T H (fun i => C*c i) n hentry hdiag
  have hself : (∑ i : Fin t,((C*c i)*n i)*(MarkedC4.normalGen (D i) : ℝ)) ≤ (t : ℝ)*B^2 := by
    have hh := ActualLogPeelingAndSelfCost.total_diagonal_self_cost_le F D horder
    simpa only [hdiag,Fintype.card_fin] using hh
  have hoff : (∑ i : Fin t,(∑ j ∈ earlier i,((C*c i)-(C*c j))*n j)*
      (MarkedC4.normalGen (D i) : ℝ))=
      C*(∑ i : Fin t,∑ j : Fin t,
        if j < i then (c i-c j)*n j*(MarkedC4.normalGen (D i) : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [earlier,Finset.sum_filter,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j < i
    · have hjv : j.val < i.val := hji
      simp only [if_pos hji,if_pos hjv]
      ring
    · have hjv : ¬j.val < i.val := hji
      simp only [if_neg hji,if_neg hjv,zero_mul,mul_zero]
  have heq : (∑ i : Fin t,((C*c i)*n i+
      ∑ j ∈ earlier i,((C*c i)-(C*c j))*n j)*(MarkedC4.normalGen (D i) : ℝ))=
      (∑ i : Fin t,((C*c i)*n i)*(MarkedC4.normalGen (D i) : ℝ))+
        ∑ i : Fin t,(∑ j ∈ earlier i,((C*c i)-(C*c j))*n j)*
          (MarkedC4.normalGen (D i) : ℝ) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  apply hcount.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  rw [heq,hoff]
  have hm := mul_le_mul_of_nonneg_left henergy hC
  linarith

end SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauCount
