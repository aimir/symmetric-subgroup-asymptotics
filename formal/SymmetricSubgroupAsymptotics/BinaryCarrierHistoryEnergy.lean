import SymmetricSubgroupAsymptotics.JointCapacityHistory
import SymmetricSubgroupAsymptotics.BinaryCarrierConeBounds

/-! From separately certified numerical rows to the six-colour energy.
The row capacities, colour assignments and masses remain explicit data.
No actual group row, physical profile, or catalogue completeness is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierHistoryEnergy

open BinaryCarrierCone JointCapacityRow

def colorMass {t : ℕ} (color : Fin t → Fin 6) (u : Fin t → ℝ) (c : Fin 6) : ℝ :=
  ∑ i, if color i = c then u i else 0

theorem colorMass_nonneg {t : ℕ} (color : Fin t → Fin 6) (u : Fin t → ℝ)
    (hu : ∀ i, 0 ≤ u i) (c : Fin 6) : 0 ≤ colorMass color u c := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hu i
  · exact le_rfl

/-- Exact aggregation by colour, retaining each individual mass once. -/
theorem colorMass_sum_mul {t : ℕ} (color : Fin t → Fin 6) (u : Fin t → ℝ)
    (f : Fin 6 → ℝ) :
    (∑ c, colorMass color u c * f c) = ∑ i, u i * f (color i) := by
  classical
  simp only [colorMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul]
  simp

theorem colorMass_sum {t : ℕ} (color : Fin t → Fin 6) (u : Fin t → ℝ) :
    (∑ c, colorMass color u c) = ∑ i, u i := by
  simpa only [mul_one] using colorMass_sum_mul color u (fun _ => 1)

/-- Bilinear colour aggregation is exact, before any diagonal is added. -/
theorem quadratic_colorMass {t : ℕ} (color : Fin t → Fin 6) (u : Fin t → ℝ)
    (M : Fin 6 → Fin 6 → ℝ) :
    quadratic M (colorMass color u) =
      ∑ i, ∑ a, M (color i) (color a) * u i * u a := by
  unfold quadratic
  have hrow (c : Fin 6) :
      (∑ d, M c d * colorMass color u c * colorMass color u d) =
        colorMass color u c * ∑ d, colorMass color u d * M c d := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  simp_rw [hrow]
  rw [colorMass_sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [colorMass_sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem pairMatrix64_symmetric (c d : Fin 6) : pairMatrix64 c d = pairMatrix64 d c := by
  fin_cases c <;> fin_cases d <;> norm_num [pairMatrix64]

theorem pairMatrix64_diagonal_nonneg (c : Fin 6) : 0 ≤ pairMatrix64 c c := by
  fin_cases c <;> norm_num [pairMatrix64]

/-- Twice the strict unordered-pair sum is at most the full double sum.
Only the diagonal needs nonnegativity; symmetry accounts for the two orders. -/
theorem twice_strict_pair_sum_le {t : ℕ} (w : Fin t → Fin t → ℝ)
    (hsymm : ∀ i a, w i a = w a i) (hdiag : ∀ i, 0 ≤ w i i) :
    2 * (∑ i, ∑ a ∈ Finset.univ.filter (fun a => a < i), w i a) ≤
      ∑ i, ∑ a, w i a := by
  classical
  have hpoint (i a : Fin t) :
      (if a < i then w i a else 0) + (if i < a then w i a else 0) ≤ w i a := by
    rcases lt_trichotomy a i with h | h | h
    · simp only [h, not_lt_of_ge h.le, if_true, if_false, add_zero, le_refl]
    · subst a
      simpa using hdiag i
    · simp only [h, not_lt_of_ge h.le, if_true, if_false, zero_add, le_refl]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin t)))
    (fun i _ => Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin t))) (fun a _ => hpoint i a))
  have hswap :
      (∑ i : Fin t, ∑ a : Fin t, if i < a then w i a else 0) =
        ∑ i : Fin t, ∑ a : Fin t, if a < i then w i a else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    split_ifs
    · exact hsymm a i
    · rfl
  simp only [Finset.sum_add_distrib, hswap] at hsum
  simp only [Finset.sum_filter]
  linarith

/-- Individual pair certificates imply the quadratic majorant. There is
no certificate requirement on a row paired with itself: its nonnegative
matrix diagonal is added only at this aggregation step. -/
theorem pair_sum_le_quadratic {t : ℕ} (rows : Fin t → JointCapacityRow)
    (color : Fin t → Fin 6) (u : Fin t → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hpair : ∀ a i, a < i → symmetricSupport (rows a) (rows i) ≤
      u a * u i * pairMatrix64 (color a) (color i) / 64) :
    (∑ i, ∑ a ∈ Finset.univ.filter (fun a => a < i),
      symmetricSupport (rows a) (rows i)) ≤
        quadratic pairMatrix64 (colorMass color u) / 128 := by
  classical
  let w (i a : Fin t) := pairMatrix64 (color i) (color a) * u i * u a
  have hsymm (i a : Fin t) : w i a = w a i := by
    dsimp [w]
    rw [pairMatrix64_symmetric (color i) (color a)]
    ring
  have hdiag (i : Fin t) : 0 ≤ w i i :=
    mul_nonneg (mul_nonneg (pairMatrix64_diagonal_nonneg (color i)) (hu i)) (hu i)
  have hdouble := twice_strict_pair_sum_le w hsymm hdiag
  have hquad : (∑ i, ∑ a, w i a) = quadratic pairMatrix64 (colorMass color u) :=
    (quadratic_colorMass color u pairMatrix64).symm
  rw [hquad] at hdouble
  have hscale :
      64 * (∑ i, ∑ a ∈ Finset.univ.filter (fun a => a < i),
        symmetricSupport (rows a) (rows i)) ≤
        ∑ i, ∑ a ∈ Finset.univ.filter (fun a => a < i), w i a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have h := hpair a i (Finset.mem_filter.mp ha).2
    have he : w i a = u a * u i * pairMatrix64 (color a) (color i) := by
      dsimp [w]
      rw [pairMatrix64_symmetric (color i) (color a)]
      ring
    rw [he]
    linarith
  linarith

/-- The actual numerical prefix tilts of a finite row assignment. -/
def finiteHistoryCost {t : ℕ} (rows : Fin t → JointCapacityRow) (x y z : ℝ) : ℝ :=
  ∑ i, (rows i).cost
    (x + ∑ a ∈ Finset.univ.filter (fun a => a < i), (rows a).c)
    (y + ∑ a ∈ Finset.univ.filter (fun a => a < i), (rows a).g) z

theorem finiteHistoryCost_terminal_le {t : ℕ} (rows : Fin t → JointCapacityRow)
    (j ell : ℝ) :
    finiteHistoryCost rows (j-ell) 0 ell ≤
      (∑ i, (ell * (((rows i).k : ℝ) + (max (rows i).m (rows i).a₂ : ℕ)) +
        ((rows i).k : ℝ) * max (j-2*ell) 0)) +
      ∑ i, ∑ a ∈ Finset.univ.filter (fun a => a < i),
        symmetricSupport (rows a) (rows i) := by
  classical
  unfold finiteHistoryCost
  calc
    _ ≤ ∑ i, ((ell * (((rows i).k : ℝ) + (max (rows i).m (rows i).a₂ : ℕ)) +
        ((rows i).k : ℝ) * max (j-2*ell) 0) +
        ∑ a ∈ Finset.univ.filter (fun a => a < i),
          symmetricSupport (rows a) (rows i)) := by
      apply Finset.sum_le_sum
      intro i _
      have hs := jointCapacitySupport_sum_le
        (Finset.univ.filter (fun a : Fin t => a < i))
        (rows i).k (rows i).n (rows i).m (fun a => (rows a).c) (fun a => (rows a).g)
      have hp := hs.trans (Finset.sum_le_sum fun a _ =>
        directedSupport_le_symmetricSupport (rows a) (rows i))
      exact ((rows i).cost_shift_le (j-ell) 0 ell _ _).trans
        (add_le_add ((rows i).cost_terminal_le j ell) hp)
    _ = _ := Finset.sum_add_distrib

/-- The independent k and max(m,a₂) certificates bound only the initial
marks. The positive part is retained on the whole rectangle, including j < ell. -/
theorem initial_marks_le {t : ℕ} (rows : Fin t → JointCapacityRow)
    (color : Fin t → Fin 6) (u : Fin t → ℝ) (j ell : ℝ) (hell : 0 ≤ ell)
    (hk : ∀ i, ((rows i).k : ℝ) ≤ u i * alpha (color i))
    (hb : ∀ i, ((max (rows i).m (rows i).a₂ : ℕ) : ℝ) ≤ u i * beta (color i)) :
    (∑ i, (ell * (((rows i).k : ℝ) + (max (rows i).m (rows i).a₂ : ℕ)) +
      ((rows i).k : ℝ) * max (j-2*ell) 0)) ≤
    ∑ c, colorMass color u c *
      (ell * (alpha c + beta c) + alpha c * max (j-2*ell) 0) := by
  rw [colorMass_sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h1 := mul_le_mul_of_nonneg_left (add_le_add (hk i) (hb i)) hell
  have h2 := mul_le_mul_of_nonneg_right (hk i) (le_max_right (j-2*ell) 0)
  calc
    _ ≤ ell * (u i * alpha (color i) + u i * beta (color i)) +
        (u i * alpha (color i)) * max (j-2*ell) 0 := add_le_add h1 h2
    _ = _ := by ring

theorem historyCost_le_marks_add_quadratic {t : ℕ} (rows : Fin t → JointCapacityRow)
    (color : Fin t → Fin 6) (u : Fin t → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hk : ∀ i, ((rows i).k : ℝ) ≤ u i * alpha (color i))
    (hb : ∀ i, ((max (rows i).m (rows i).a₂ : ℕ) : ℝ) ≤ u i * beta (color i))
    (hpair : ∀ a i, a < i → symmetricSupport (rows a) (rows i) ≤
      u a * u i * pairMatrix64 (color a) (color i) / 64)
    (j ell : ℝ) (hell : 0 ≤ ell) :
    finiteHistoryCost rows (j-ell) 0 ell ≤
      (∑ c, colorMass color u c *
        (ell * (alpha c + beta c) + alpha c * max (j-2*ell) 0)) +
      quadratic pairMatrix64 (colorMass color u) / 128 :=
  (finiteHistoryCost_terminal_le rows j ell).trans
    (add_le_add (initial_marks_le rows color u j ell hell hk hb)
      (pair_sum_le_quadratic rows color u hu hpair))

/-- The certified rows supply the energy expression; it is a conclusion,
not a supplied majorant. No upper relation between j and ell is used here. -/
theorem critical_add_historyCost_le_energy {t : ℕ} (rows : Fin t → JointCapacityRow)
    (color : Fin t → Fin 6) (u : Fin t → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hk : ∀ i, ((rows i).k : ℝ) ≤ u i * alpha (color i))
    (hb : ∀ i, ((max (rows i).m (rows i).a₂ : ℕ) : ℝ) ≤ u i * beta (color i))
    (hpair : ∀ a i, a < i → symmetricSupport (rows a) (rows i) ≤
      u a * u i * pairMatrix64 (color a) (color i) / 64)
    (R j ell : ℝ) (hell : 0 ≤ ell) :
    ell * (R/2-ell) + (j-ell)*(R-j) + finiteHistoryCost rows (j-ell) 0 ell ≤
      energy R j ell (colorMass color u) := by
  have h := historyCost_le_marks_add_quadratic rows color u hu hk hb hpair j ell hell
  unfold energy
  linarith

/-- Exact physical-mass substitution on the original full rectangle.
The equality sum u = 4T remains a separate numerical binding obligation. -/
theorem critical_add_historyCost_le_reserve {t : ℕ} (rows : Fin t → JointCapacityRow)
    (color : Fin t → Fin 6) (u : Fin t → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hk : ∀ i, ((rows i).k : ℝ) ≤ u i * alpha (color i))
    (hb : ∀ i, ((max (rows i).m (rows i).a₂ : ℕ) : ℝ) ≤ u i * beta (color i))
    (hpair : ∀ a i, a < i → symmetricSupport (rows a) (rows i) ≤
      u a * u i * pairMatrix64 (color a) (color i) / 64)
    (R T j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R/2)
    (hmass : ∑ i, u i = 4*T) :
    ell * (R/2-ell) + (j-ell)*(R-j) + finiteHistoryCost rows (j-ell) 0 ell ≤
      (R+4*T)^2/4 - (25/82)*R*T - (29/164)*T^2 := by
  apply (critical_add_historyCost_le_energy rows color u hu hk hb hpair R j ell hell.1).trans
  apply energy_le_reserve R T j ell (colorMass color u)
    (colorMass_nonneg color u hu) hj hell
  exact (colorMass_sum color u).trans hmass

end SymmetricSubgroupAsymptotics.BinaryCarrierHistoryEnergy
