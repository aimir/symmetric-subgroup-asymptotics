import SymmetricSubgroupAsymptotics.MarkedC4PsiAnalysis

/-!
# Compressing physical abelian columns around the two marked columns

The auxiliary `C4^r` factor contributes `r` to each of the first two target
columns.  All physical abelian column mass can be moved into the first column
without decreasing the Hall exponent, while the second auxiliary column is
retained.  This is the exact column exchange used in the Case-I splice.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- Collapse any finite packet of target-column mass into a larger first
column when every corresponding source column is at most the first source
column. -/
theorem psi_add_sum_le_collapse
    {ι : Type*} (s : Finset ι) (v x : ι → ℝ) {V X : ℝ}
    (hV : 0 ≤ V)
    (hv : ∀ i ∈ s, 0 ≤ v i)
    (hx : ∀ i ∈ s, 0 ≤ x i)
    (hxX : ∀ i ∈ s, x i ≤ X) :
    psi V X + ∑ i ∈ s, psi (v i) (x i) ≤
      psi (V + ∑ i ∈ s, v i) X := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsum : 0 ≤ ∑ j ∈ s, v j :=
        Finset.sum_nonneg fun j hj => hv j (Finset.mem_insert_of_mem hj)
      have hprev := ih
        (fun j hj => hv j (Finset.mem_insert_of_mem hj))
        (fun j hj => hx j (Finset.mem_insert_of_mem hj))
        (fun j hj => hxX j (Finset.mem_insert_of_mem hj))
      have hadd := psi_superadd
        (v := V + ∑ j ∈ s, v j) (w := v i) (x := X) (x' := x i)
        (add_nonneg hV hsum) (hv i (Finset.mem_insert_self i s))
        (hx i (Finset.mem_insert_self i s))
        (hxX i (Finset.mem_insert_self i s))
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc
        psi V X + (psi (v i) (x i) + ∑ j ∈ s, psi (v j) (x j)) =
            (psi V X + ∑ j ∈ s, psi (v j) (x j)) + psi (v i) (x i) := by ring
        _ ≤ psi (V + ∑ j ∈ s, v j) X + psi (v i) (x i) :=
          add_le_add hprev le_rfl
        _ ≤ psi (V + ∑ j ∈ s, v j + v i) X := hadd
        _ = psi (V + (v i + ∑ j ∈ s, v j)) X := by
          congr 1
          ring

/-- **Two-column physical packet compression.**  The first two physical
columns are `a₀ ≥ a₁`; later physical columns form the packet `v`.  If their
total mass is at most `a/2`, then after adjoining `C4^r` the complete Hall
exponent is bounded by the two retained source columns at target capacities
`a/2+r` and `r`. -/
theorem psi_twoColumn_packet_compression
    {ι : Type*} (s : Finset ι) (v x : ι → ℝ)
    {a a₀ a₁ r x₀ x₁ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (ha₁₀ : a₁ ≤ a₀)
    (hr : 0 ≤ r) (hx₀ : 0 ≤ x₀) (hx₁ : 0 ≤ x₁) (hx₁₀ : x₁ ≤ x₀)
    (hv : ∀ i ∈ s, 0 ≤ v i)
    (hx : ∀ i ∈ s, 0 ≤ x i)
    (hx₀' : ∀ i ∈ s, x i ≤ x₀)
    (hmass : a₀ + a₁ + ∑ i ∈ s, v i ≤ a / 2) :
    psi (a₀ + r) x₀ + psi (a₁ + r) x₁ +
        ∑ i ∈ s, psi (v i) (x i) ≤
      psi (a / 2 + r) x₀ + psi r x₁ := by
  have hexchange := psi_exchange
    (V := a₀ + r) (u := r) (δ := a₁) (x := x₀) (x' := x₁)
    hr ha₁ hx₁ hx₁₀ (by linarith)
  have hsum : 0 ≤ ∑ i ∈ s, v i := Finset.sum_nonneg fun i hi => hv i hi
  have hcollapse := psi_add_sum_le_collapse s v x
    (add_nonneg (add_nonneg ha₀ ha₁) hr) hv hx hx₀'
  have hmono : psi (a₀ + a₁ + r + ∑ i ∈ s, v i) x₀ ≤
      psi (a / 2 + r) x₀ := by
    apply psi_mono_left
    · positivity
    · linarith
    · exact hx₀
  calc
    psi (a₀ + r) x₀ + psi (a₁ + r) x₁ + ∑ i ∈ s, psi (v i) (x i) =
        (psi (a₀ + r) x₀ + psi (r + a₁) x₁) +
          ∑ i ∈ s, psi (v i) (x i) := by rw [add_comm a₁ r]
    _ ≤ (psi (a₀ + r + a₁) x₀ + psi r x₁) +
          ∑ i ∈ s, psi (v i) (x i) :=
      add_le_add hexchange le_rfl
    _ = (psi (a₀ + a₁ + r) x₀ +
          ∑ i ∈ s, psi (v i) (x i)) + psi r x₁ := by
      have harg : a₀ + r + a₁ = a₀ + a₁ + r := by ring
      rw [harg]
      ring
    _ ≤ psi (a₀ + a₁ + r + ∑ i ∈ s, v i) x₀ + psi r x₁ :=
      add_le_add hcollapse le_rfl
    _ ≤ psi (a / 2 + r) x₀ + psi r x₁ :=
      add_le_add hmono le_rfl

end MarkedC4
end SymmetricSubgroupAsymptotics

end
