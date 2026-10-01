import SymmetricSubgroupAsymptotics.MarkedC4CaseISplice
import SymmetricSubgroupAsymptotics.MarkedC4ColumnCompression

/-!
# Complete numerical Case I with retained source columns

After the physical Hall columns have been compressed, the Hall exponent is
`Psi(a/2+r,d(L)) + Psi(r,c(L))`.  This file combines its two maximizing
ranks with the simultaneous filtration bounds on `d(L)` and `d(L)+c(L)` and
then invokes the layer-cake splice.  No source column is maximized separately.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- The maximizing Hall rank is monotone in both target and source column. -/
theorem ystar_mono {v v' x x' : ℝ}
    (hvv : v ≤ v') (hxx : x ≤ x') :
    ystar v x ≤ ystar v' x' := by
  unfold ystar
  split_ifs with h h'
  · exact hvv
  · linarith
  · linarith
  · linarith

/-- **Complete Case-I exponent.**  `sourceFirst` and `sourceSecond` are the
actual first two binary columns of the retained nonabelian source.  The two
filtration inequalities are charged jointly against the same diagonal ranks,
and the compressed Hall packet is then paid by `markedF`. -/
theorem caseI_entropy_add_compressedHall_le
    (c n d : ℕ → ℝ) (t : ℕ)
    {a r sourceFirst sourceSecond : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hfirst : 0 ≤ sourceFirst) (hsecond : 0 ≤ sourceSecond)
    (hsecondFirst : sourceSecond ≤ sourceFirst)
    (hfirstCap : sourceFirst ≤ ∑ m ∈ Finset.range t, d m)
    (hjointCap : sourceFirst + sourceSecond ≤
      ∑ m ∈ Finset.range t, min (2 * d m) (c m * n m))
    (hn : ∀ m < t, 0 ≤ n m)
    (hc0 : ∀ m < t, 0 ≤ c m) (hc1 : ∀ m < t, c m ≤ 1)
    (hmono : ∀ j m, j ≤ m → m < t → c j ≤ c m)
    (hd0 : ∀ m < t, 0 ≤ d m)
    (hd1 : ∀ m < t, d m ≤ n m / 4)
    (hd2 : ∀ m < t, d m ≤ c m * n m) :
    (∑ m ∈ Finset.range t,
        ∑ j ∈ Finset.range m, (c m - c j) * n j * d m) +
      psi (a / 2 + r) sourceFirst + psi r sourceSecond ≤
        markedF (a + prefixWeight n t) r := by
  let α := ystar (a / 2 + r) sourceFirst
  let β := ystar r sourceSecond
  have hv₁0 : 0 ≤ a / 2 + r := by positivity
  have hα0 : 0 ≤ α := ystar_nonneg hv₁0 hfirst
  have hβ0 : 0 ≤ β := ystar_nonneg hr hsecond
  have hαv : α ≤ a / 2 + r := ystar_le
  have hβr : β ≤ r := ystar_le
  have hβα : β ≤ α := by
    exact ystar_mono (by linarith) hsecondFirst
  have hweighted :
      (α - β) * sourceFirst + β * (sourceFirst + sourceSecond) ≤
        (α - β) * (∑ m ∈ Finset.range t, d m) +
          β * (∑ m ∈ Finset.range t, min (2 * d m) (c m * n m)) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hfirstCap (sub_nonneg.mpr hβα))
      (mul_le_mul_of_nonneg_left hjointCap hβ0)
  have hsplice := caseI_joint_splice_exact c n d t ha hr hβ0 hβα hαv hβr
    hn hc0 hc1 hmono hd0 hd1 hd2
  rw [psi_eq (a / 2 + r) sourceFirst, psi_eq r sourceSecond]
  change _ + α * (a / 2 + r - α + sourceFirst) +
      β * (r - β + sourceSecond) ≤ _
  nlinarith

end MarkedC4
end SymmetricSubgroupAsymptotics

end
