import SymmetricSubgroupAsymptotics.MarkedC4ActualTableauEntropy

/-! Actual tableau density subtraction. Support and diagonal identities
are derived from the literal subgroup. Local density comparisons concern
actual entry orders; an enumeration or entropy bound is never a premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualTableauDensityEntropy
open ActualSubdirectFiltration ActualEfficientRowIncidence
open ActualPrefixOrders ActualTableauRowIncidence ActualTableauEntropy

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (D : ∀ i,Subgroup (F i)) (T : ∀ i j : Fin t,Subgroup (F j))

def earlier (i : Fin t) : Finset (Fin t) := Finset.univ.filter (fun j => j.val < i.val)

theorem entry_above_eq_bot (H : TableauFamily F D T) (i j : Fin t)
    (hij : i.val < j.val) : T i j=⊥ := by
  rw [← H.property i j]
  apply le_antisymm _ bot_le
  rintro q ⟨h,hh,rfl⟩
  apply Subgroup.mem_bot.mpr
  exact (mem_prefix F H.val.val (i.val+1) h).mp hh j (by omega)

theorem diagonal_entry (H : TableauFamily F D T) (i : Fin t) : T i i=D i :=
  (H.property i i).symm.trans (H.val.property.2.2 i)

theorem rowLog_eq_sum (i : Fin t) :
    rowLog F T i=∑ j : Fin t,Real.logb 2 (Nat.card (T i j)) := by
  unfold rowLog
  rw [Nat.cast_prod,Real.logb_prod]
  intro j _
  exact_mod_cast (Nat.card_pos (α := T i j)).ne'

/-- All preceding actual diagonal orders, in original physical labels. -/
theorem prefixLog_eq_earlier (H : TableauFamily F D T) (i : Fin t) :
    prefixLog F H.val.val i.val=
      ∑ j ∈ earlier i,Real.logb 2 (Nat.card (D j)) := by
  rw [prefixLog_eq_sum F H.val.val i.val (Nat.le_of_lt i.isLt)]
  symm
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  · intro j hj k hk h
    exact Fin.ext h
  · intro m hm
    have hmi : m < i.val := Finset.mem_range.mp hm
    refine ⟨⟨m,hmi.trans i.isLt⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmi⟩
  · intro j hj
    simp only [layerLog,dif_pos j.isLt,H.val.property.2.2 j]

private theorem leIndices_eq_insert (i : Fin t) :
    Finset.univ.filter (fun j : Fin t => j.val ≤ i.val)=insert i (earlier i) := by
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,earlier]
  constructor
  · intro h
    by_cases he : j.val=i.val
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (by omega)
  · rintro (rfl | h) <;> omega

/-- The local hypotheses are comparisons of ACTUAL coordinate-image
orders, precisely the comparisons supplied by physical factor peeling. -/
theorem rowLog_le_density (H : TableauFamily F D T) (c n : Fin t → ℝ)
    (hentry : ∀ i j,j.val ≤ i.val →
      Real.logb 2 (Nat.card (T i j))≤c i*n j) (i : Fin t) :
    rowLog F T i≤c i*n i+∑ j ∈ earlier i,c i*n j := by
  rw [rowLog_eq_sum F T i]
  have hs : (∑ j : Fin t,Real.logb 2 (Nat.card (T i j)))=
      ∑ j ∈ Finset.univ.filter (fun j : Fin t => j.val ≤ i.val),
        Real.logb 2 (Nat.card (T i j)) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hjnot
    have hij : i.val < j.val := by
      have hh : ¬j.val ≤ i.val := by
        intro h
        exact hjnot (Finset.mem_filter.mpr ⟨hj,h⟩)
      omega
    rw [entry_above_eq_bot F D T H i j hij]
    simp
  rw [hs]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin t => j.val ≤ i.val),c i*n j :=
      Finset.sum_le_sum (fun j hj => hentry i j (Finset.mem_filter.mp hj).2)
    _ = _ := by
      rw [leIndices_eq_insert,Finset.sum_insert]
      simp [earlier]

/-- The actual denominator subtracts the preceding diagonal densities.
Only the diagonal self-cost remains beside the sharp off-diagonal term. -/
theorem row_minus_prefix_le (H : TableauFamily F D T) (c n : Fin t → ℝ)
    (hentry : ∀ i j,j.val ≤ i.val →
      Real.logb 2 (Nat.card (T i j))≤c i*n j)
    (hdiag : ∀ j,Real.logb 2 (Nat.card (D j))=c j*n j) (i : Fin t) :
    rowLog F T i-prefixLog F H.val.val i.val ≤
      c i*n i+∑ j ∈ earlier i,(c i-c j)*n j := by
  rw [prefixLog_eq_earlier F D T H i]
  have hh := rowLog_le_density F D T H c n hentry i
  have he : (∑ j ∈ earlier i,c i*n j)-
      (∑ j ∈ earlier i,Real.logb 2 (Nat.card (D j)))=
        ∑ j ∈ earlier i,(c i-c j)*n j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hdiag j]
    ring
  linarith

/-- The original literal fixed-tableau family now has the sharp density
entropy bound, including its explicit diagonal self-cost. -/
theorem card_le_density_entropy (H : TableauFamily F D T) (c n : Fin t → ℝ)
    (hentry : ∀ i j,j.val ≤ i.val →
      Real.logb 2 (Nat.card (T i j))≤c i*n j)
    (hdiag : ∀ j,Real.logb 2 (Nat.card (D j))=c j*n j) :
    (Nat.card (TableauFamily F D T) : ℝ) ≤
      (2 : ℝ)^(∑ i : Fin t,
        (c i*n i+∑ j ∈ earlier i,(c i-c j)*n j)*(normalGen (D i) : ℝ)) := by
  apply (card_le_two_pow_entropy F D T H).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
  unfold entropy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_right
    (row_minus_prefix_le F D T H c n hentry hdiag i) (Nat.cast_nonneg (normalGen (D i)))
  nlinarith

end SymmetricSubgroupAsymptotics.MarkedC4.ActualTableauDensityEntropy
