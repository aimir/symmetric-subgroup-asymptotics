import SymmetricSubgroupAsymptotics.PGroupOrderedTransversal
import SymmetricSubgroupAsymptotics.CoinducedLeadingCoordinates
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Ordered coordinates for the actual recursive coset grid

The recursive highest-coordinate-first order is preserved by the explicit
radix code into `Fin (p^n)`. The separate tuple equivalence preserves
coordinatewise comparison. Reindexing the actual right transversal changes
only its labels: its representatives, H-factors, uniqueness, and triangular
equations all come from the original `OrderedCosetData`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open CoinducedLeadingCoordinates

/-- The numeric code is `low + p^n * high`, matching the recursive strict
order rather than an arbitrary enumeration of this finite set. -/
def primeCosetGridCode (p : ℕ) : (n : ℕ) → PrimeCosetGrid p n ≃ Fin (p^n)
  | 0 => {
      toFun := fun _ => ⟨0, by simp⟩
      invFun := fun _ => ()
      left_inv := fun a => @Subsingleton.elim Unit inferInstance () a
      right_inv := by
        intro a
        apply Fin.ext
        have ha := a.isLt
        simp only [pow_zero] at ha
        change 0=a.val
        omega }
  | n+1 =>
      ((Equiv.prodCongr (Equiv.refl (Fin p)) (primeCosetGridCode p n)).trans
        finProdFinEquiv).trans (finCongr (pow_succ' p n).symm)

@[simp] theorem primeCosetGridCode_succ_val (p n : ℕ) (a : PrimeCosetGrid p (n+1)) :
    (primeCosetGridCode p (n+1) a).val =
      (primeCosetGridCode p n a.2).val + p^n*a.1.val := rfl

private theorem label_lt_iff {m n : ℕ} (a b : Fin m) (i j : Fin n) :
    label a i < label b j ↔ a<b ∨ a=b ∧ i<j := by
  constructor
  · exact label_lt_cases
  · rintro (hab | ⟨rfl, hij⟩)
    · exact label_row_lt hab i j
    · exact label_fibre_lt a hij

/-- The numeric code preserves and reflects the complete recursive order. -/
theorem primeCosetGridCode_lt_iff (p n : ℕ) (a b : PrimeCosetGrid p n) :
    primeCosetGridCode p n a < primeCosetGridCode p n b ↔
      primeCosetGridLT p n a b := by
  induction n with
  | zero =>
    change (0:ℕ)<0 ↔ False
    simp
  | succ n ih =>
    change label a.1 (primeCosetGridCode p n a.2) <
        label b.1 (primeCosetGridCode p n b.2) ↔
      a.1<b.1 ∨ a.1=b.1 ∧ primeCosetGridLT p n a.2 b.2
    rw [label_lt_iff, ih]

/-- The first tuple coordinate is the highest subgroup coordinate. -/
def primeCosetGridTuple (p : ℕ) : (n : ℕ) → PrimeCosetGrid p n ≃ (Fin n → Fin p)
  | 0 => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := fun a => @Subsingleton.elim Unit inferInstance () a
      right_inv := by intro a; funext i; exact Fin.elim0 i }
  | n+1 =>
      (Equiv.prodCongr (Equiv.refl (Fin p)) (primeCosetGridTuple p n)).trans
        (Fin.consEquiv (fun _ : Fin (n+1) => Fin p))

/-- The grid relation is exactly componentwise comparison of the tuple. -/
theorem primeCosetGridTuple_le_iff (p n : ℕ) (a b : PrimeCosetGrid p n) :
    primeCosetGridTuple p n a ≤ primeCosetGridTuple p n b ↔
      primeCosetGridComparable p n a b := by
  induction n with
  | zero =>
    constructor
    · intro _; trivial
    · intro _ i; exact Fin.elim0 i
  | succ n ih =>
    change Fin.cons (α := fun _ : Fin (n+1) => Fin p) a.1 (primeCosetGridTuple p n a.2) ≤
        Fin.cons (α := fun _ : Fin (n+1) => Fin p) b.1 (primeCosetGridTuple p n b.2) ↔
      a.1≤b.1 ∧ primeCosetGridComparable p n a.2 b.2
    rw [Fin.cons_le_cons, ih]

/-- Componentwise grid comparison pulled back along the ordered code. -/
def primeCosetFinComparable (p n : ℕ) (a b : Fin (p^n)) : Prop :=
  primeCosetGridComparable p n
    ((primeCosetGridCode p n).symm a) ((primeCosetGridCode p n).symm b)

/-- Tuple coordinates of a numerically ordered coset row. -/
def primeCosetFinPoint (p n : ℕ) (a : Fin (p^n)) : Fin n → Fin p :=
  primeCosetGridTuple p n ((primeCosetGridCode p n).symm a)

theorem primeCosetFinComparable_iff_point_le (p n : ℕ) (a b : Fin (p^n)) :
    primeCosetFinComparable p n a b ↔
      primeCosetFinPoint p n a ≤ primeCosetFinPoint p n b :=
  (primeCosetGridTuple_le_iff p n _ _).symm

variable {G : Type*} [Group G] {p n : ℕ} {H K : Subgroup G}

/-- Install the same actual transversal on ordered finite row indices.
No representation, ambient group, subgroup, or fibre is replaced. -/
def OrderedCosetData.finRows
    (D : OrderedCosetData H K (PrimeCosetGrid p n)
      (primeCosetGridLT p n) (primeCosetGridComparable p n)) :
    OrderedCosetData H K (Fin (p^n)) (· < ·) (primeCosetFinComparable p n) where
  le := D.le
  repr := fun a => D.repr ((primeCosetGridCode p n).symm a)
  mem := fun a => D.mem _
  factor := by
    intro y hy
    obtain ⟨h, hh, a, ha⟩ := D.factor y hy
    refine ⟨h, hh, primeCosetGridCode p n a, ?_⟩
    simpa only [Equiv.symm_apply_apply] using ha
  unique := by
    intro a b hab
    apply (primeCosetGridCode p n).symm.injective
    exact D.unique _ _ hab
  triangular := by
    intro a b c hab hbc
    have hab' : primeCosetGridLT p n ((primeCosetGridCode p n).symm a)
        ((primeCosetGridCode p n).symm b) :=
      (primeCosetGridCode_lt_iff p n _ _).mp
        (by simpa only [Equiv.apply_symm_apply] using hab)
    obtain ⟨h, hh, e, hec, he⟩ := D.triangular _ _ _ hab' hbc
    refine ⟨h, hh, primeCosetGridCode p n e, ?_, ?_⟩
    · have := (primeCosetGridCode_lt_iff p n e
        ((primeCosetGridCode p n).symm c)).mpr hec
      simpa only [Equiv.apply_symm_apply] using this
    · simpa only [Equiv.symm_apply_apply] using he

end SymmetricSubgroupAsymptotics
