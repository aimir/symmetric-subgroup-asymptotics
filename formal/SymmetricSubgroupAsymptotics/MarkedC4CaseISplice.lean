import SymmetricSubgroupAsymptotics.MarkedC4ProductColumns
import SymmetricSubgroupAsymptotics.MarkedC4LayerCake

/-!
# The numerical Case-I marked-C4 splice

This is the abstract numerical theorem used after a fixed RDT tableau and a
fixed Hall quotient profile have been chosen.  The diagonal ranks are kept in
the layer-cake bound, while the two Hall ranks are optimized against those
same retained ranks.  In particular the two source columns are never replaced
by independent worst-case estimates.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- Adding `r` literal cyclic-four coordinates adds `r` to each of the first
two columns and nothing to any later column. -/
theorem col_prod_cyclicFourCoordinates (A : Type*) [CommGroup A] [Finite A]
    (r k : ℕ) :
    col (A × Multiplicative (Fin r → ZMod 4)) k =
      col A k + if k < 2 then r else 0 := by
  calc
    col (A × Multiplicative (Fin r → ZMod 4)) k =
        col A k + col (Multiplicative (Fin r → ZMod 4)) k := col_prod A _ k
    _ = _ := by rw [col_cyclicFourCoordinates]

/-- The complete scalar Case-I splice.  `α` and `β` are the two Hall ranks,
`v₁ = a/2+r` and `r` are their target-column capacities, and `B` is the
physical support of the nonabelian nonexcess tableau. -/
theorem caseI_joint_splice
    (c n d : ℕ → ℝ) (t : ℕ) {a r v₁ α β H : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hv₁ : v₁ = a / 2 + r)
    (hβ : 0 ≤ β) (hβα : β ≤ α) (hαv : α ≤ v₁) (hβr : β ≤ r)
    (hn : ∀ m < t, 0 ≤ n m)
    (hc0 : ∀ m < t, 0 ≤ c m) (hc1 : ∀ m < t, c m ≤ 1)
    (hmono : ∀ j m, j ≤ m → m < t → c j ≤ c m)
    (hd0 : ∀ m < t, 0 ≤ d m)
    (hd1 : ∀ m < t, d m ≤ n m / 4)
    (hd2 : ∀ m < t, d m ≤ c m * n m)
    (hH : H ≤ α * (v₁ - α) + β * (r - β)) :
    (∑ m ∈ Finset.range t,
        ∑ j ∈ Finset.range m, (c m - c j) * n j * d m)
      + (α - β) * ∑ m ∈ Finset.range t, d m
      + β * ∑ m ∈ Finset.range t, min (2 * d m) (c m * n m)
      + H
    ≤ markedF (a + prefixWeight n t) r := by
  let B := prefixWeight n t
  have hB : 0 ≤ B := Finset.sum_nonneg fun m hm => hn m (Finset.mem_range.mp hm)
  have htableau := layerCake_ranks c n d t hβ hβα hn hc0 hc1 hmono hd0 hd1 hd2
  have hα : 0 ≤ α := hβ.trans hβα
  have hfirst := rank_gB_le (B := B) (v := v₁) hB hα hαv
  have hsecond := rank_gB_le (B := B) (v := r) hB hβ hβr
  have hv₁0 : 0 ≤ v₁ := by rw [hv₁]; linarith
  have hsplice := splice_quadratic_le ha hB hr hv₁0 hv₁.le
  dsimp only [B] at hB htableau hfirst hsecond hsplice
  linarith

/-- The same theorem with the Hall exponent displayed in its exact quadratic
form. -/
theorem caseI_joint_splice_exact
    (c n d : ℕ → ℝ) (t : ℕ) {a r α β : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hαv : α ≤ a / 2 + r) (hβr : β ≤ r)
    (hn : ∀ m < t, 0 ≤ n m)
    (hc0 : ∀ m < t, 0 ≤ c m) (hc1 : ∀ m < t, c m ≤ 1)
    (hmono : ∀ j m, j ≤ m → m < t → c j ≤ c m)
    (hd0 : ∀ m < t, 0 ≤ d m)
    (hd1 : ∀ m < t, d m ≤ n m / 4)
    (hd2 : ∀ m < t, d m ≤ c m * n m) :
    (∑ m ∈ Finset.range t,
        ∑ j ∈ Finset.range m, (c m - c j) * n j * d m)
      + (α - β) * ∑ m ∈ Finset.range t, d m
      + β * ∑ m ∈ Finset.range t, min (2 * d m) (c m * n m)
      + α * (a / 2 + r - α) + β * (r - β)
    ≤ markedF (a + prefixWeight n t) r := by
  have := caseI_joint_splice c n d t ha hr rfl hβ hβα hαv hβr
    hn hc0 hc1 hmono hd0 hd1 hd2
    (H := α * (a / 2 + r - α) + β * (r - β)) le_rfl
  linarith

end MarkedC4
end SymmetricSubgroupAsymptotics

end
