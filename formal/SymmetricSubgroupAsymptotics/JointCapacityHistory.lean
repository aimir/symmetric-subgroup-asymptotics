import SymmetricSubgroupAsymptotics.JointCapacitySupport
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite histories of the coupled numerical support function. Rows are
arbitrary data: this module supplies no identification with actual groups,
normal subgroups, or a finite carrier catalogue. Subtraction of the terminal
mark takes place in the reals, including when the initial first mark is negative. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- Subadditivity iterated over an arbitrary finite set. -/
theorem jointCapacitySupport_sum_le {ι : Type*} (s : Finset ι)
    (k n m : ℕ) (x y : ι → ℝ) :
    jointCapacitySupport k n m (∑ i ∈ s, x i) (∑ i ∈ s, y i) ≤
      ∑ i ∈ s, jointCapacitySupport k n m (x i) (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      apply jointCapacitySupport_le
      intro δ ε _ _ _
      simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (jointCapacitySupport_subadd k n m (x a) (y a)
        (∑ i ∈ s, x i) (∑ i ∈ s, y i)).trans (add_le_add le_rfl ih)

/-- The four natural capacities and two real quotient slopes of one row.
Allowing real slopes makes the numerical estimate independent of their
eventual group-theoretic realization. -/
structure JointCapacityRow where
  k : ℕ
  n : ℕ
  m : ℕ
  a₂ : ℕ
  c : ℝ
  g : ℝ

namespace JointCapacityRow

def cost (r : JointCapacityRow) (x y z : ℝ) : ℝ :=
  z * ((r.k : ℝ) + (max r.m r.a₂ : ℕ)) +
    jointCapacitySupport r.k r.n r.m (x-z) y

/-- The contribution from an earlier row's slopes to a later row. -/
def directedSupport (earlier later : JointCapacityRow) : ℝ :=
  jointCapacitySupport later.k later.n later.m earlier.c earlier.g

def symmetricSupport (r s : JointCapacityRow) : ℝ :=
  max (directedSupport r s) (directedSupport s r)

theorem symmetricSupport_comm (r s : JointCapacityRow) :
    symmetricSupport r s = symmetricSupport s r := max_comm _ _

theorem directedSupport_nonneg (r s : JointCapacityRow) :
    0 ≤ directedSupport r s :=
  jointCapacitySupport_nonneg _ _ _ _ _

theorem directedSupport_le_symmetricSupport (r s : JointCapacityRow) :
    directedSupport r s ≤ symmetricSupport r s := le_max_left _ _

theorem cost_shift_le (r : JointCapacityRow) (x y z u v : ℝ) :
    r.cost (x+u) (y+v) z ≤
      r.cost x y z + jointCapacitySupport r.k r.n r.m u v := by
  unfold cost
  rw [show x+u-z = (x-z)+u by ring]
  have h := jointCapacitySupport_subadd r.k r.n r.m (x-z) y u v
  linarith

theorem cost_prefix_le (rows : ℕ → JointCapacityRow) (i : ℕ) (x y z : ℝ) :
    (rows i).cost (x + ∑ a ∈ Finset.range i, (rows a).c)
      (y + ∑ a ∈ Finset.range i, (rows a).g) z ≤
      (rows i).cost x y z +
        ∑ a ∈ Finset.range i, directedSupport (rows a) (rows i) := by
  exact ((rows i).cost_shift_le x y z _ _).trans
    (add_le_add le_rfl
      (jointCapacitySupport_sum_le (Finset.range i) (rows i).k (rows i).n
        (rows i).m (fun a => (rows a).c) (fun a => (rows a).g)))

/-- These are precisely the successive tilts used by the local transition.
Nonnegative slopes preserve admissible nonnegative marks. The support bounds
below are stronger and do not require the slopes themselves to be nonnegative. -/
theorem prefix_tilts_ge (rows : ℕ → JointCapacityRow) (i : ℕ) (x y : ℝ)
    (hc : ∀ a < i, 0 ≤ (rows a).c) (hg : ∀ a < i, 0 ≤ (rows a).g) :
    x ≤ x + ∑ a ∈ Finset.range i, (rows a).c ∧
      y ≤ y + ∑ a ∈ Finset.range i, (rows a).g := by
  constructor
  · exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun a ha => hc a (Finset.mem_range.mp ha))
  · exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun a ha => hg a (Finset.mem_range.mp ha))

def historyCost (rows : ℕ → JointCapacityRow) (t : ℕ) (x y z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range t,
    (rows i).cost (x + ∑ a ∈ Finset.range i, (rows a).c)
      (y + ∑ a ∈ Finset.range i, (rows a).g) z

/-- Each earlier/later pair appears exactly once, in its actual peel order. -/
theorem historyCost_le_directed (rows : ℕ → JointCapacityRow) (t : ℕ)
    (x y z : ℝ) :
    historyCost rows t x y z ≤
      (∑ i ∈ Finset.range t, (rows i).cost x y z) +
        ∑ i ∈ Finset.range t,
          ∑ a ∈ Finset.range i, directedSupport (rows a) (rows i) := by
  unfold historyCost
  calc
    _ ≤ ∑ i ∈ Finset.range t, ((rows i).cost x y z +
        ∑ a ∈ Finset.range i, directedSupport (rows a) (rows i)) :=
      Finset.sum_le_sum fun i _ => cost_prefix_le rows i x y z
    _ = _ := Finset.sum_add_distrib

theorem historyCost_le_symmetric (rows : ℕ → JointCapacityRow) (t : ℕ)
    (x y z : ℝ) :
    historyCost rows t x y z ≤
      (∑ i ∈ Finset.range t, (rows i).cost x y z) +
        ∑ i ∈ Finset.range t,
          ∑ a ∈ Finset.range i, symmetricSupport (rows a) (rows i) := by
  apply (historyCost_le_directed rows t x y z).trans
  apply add_le_add le_rfl
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
    directedSupport_le_symmetricSupport (rows a) (rows i)

/-- Uniform terminal initial-mark bound, with no comparison between j and ell. -/
theorem cost_terminal_le (r : JointCapacityRow) (j ell : ℝ) :
    r.cost (j-ell) 0 ell ≤
      ell * ((r.k : ℝ) + (max r.m r.a₂ : ℕ)) +
        (r.k : ℝ) * max (j-2*ell) 0 := by
  unfold cost
  rw [show j-ell-ell = j-2*ell by ring]
  exact add_le_add le_rfl (jointCapacitySupport_zero_second_le r.k r.n r.m _)

theorem historyCost_terminal_le_directed (rows : ℕ → JointCapacityRow) (t : ℕ)
    (j ell : ℝ) :
    historyCost rows t (j-ell) 0 ell ≤
      (∑ i ∈ Finset.range t,
        (ell * (((rows i).k : ℝ) + (max (rows i).m (rows i).a₂ : ℕ)) +
          ((rows i).k : ℝ) * max (j-2*ell) 0)) +
        ∑ i ∈ Finset.range t,
          ∑ a ∈ Finset.range i, directedSupport (rows a) (rows i) := by
  exact (historyCost_le_directed rows t (j-ell) 0 ell).trans
    (add_le_add (Finset.sum_le_sum fun i _ =>
      cost_terminal_le (rows i) j ell) le_rfl)

theorem historyCost_terminal_le_symmetric (rows : ℕ → JointCapacityRow) (t : ℕ)
    (j ell : ℝ) :
    historyCost rows t (j-ell) 0 ell ≤
      (∑ i ∈ Finset.range t,
        (ell * (((rows i).k : ℝ) + (max (rows i).m (rows i).a₂ : ℕ)) +
          ((rows i).k : ℝ) * max (j-2*ell) 0)) +
        ∑ i ∈ Finset.range t,
          ∑ a ∈ Finset.range i, symmetricSupport (rows a) (rows i) := by
  exact (historyCost_le_symmetric rows t (j-ell) 0 ell).trans
    (add_le_add (Finset.sum_le_sum fun i _ =>
      cost_terminal_le (rows i) j ell) le_rfl)

/-- In particular, j < ell is included: the negative first support mark
has zero initial cost. Only its later prefix interactions remain. -/
theorem historyCost_terminal_lt_le (rows : ℕ → JointCapacityRow) (t : ℕ)
    (j ell : ℝ) (hell : 0 ≤ ell) (hj : j < ell) :
    historyCost rows t (j-ell) 0 ell ≤
      (∑ i ∈ Finset.range t,
        ell * (((rows i).k : ℝ) + (max (rows i).m (rows i).a₂ : ℕ))) +
        ∑ i ∈ Finset.range t,
          ∑ a ∈ Finset.range i, symmetricSupport (rows a) (rows i) := by
  have h : j-2*ell ≤ 0 := by linarith
  simpa only [max_eq_right h, mul_zero, add_zero] using
    historyCost_terminal_le_symmetric rows t j ell

end JointCapacityRow
end SymmetricSubgroupAsymptotics
