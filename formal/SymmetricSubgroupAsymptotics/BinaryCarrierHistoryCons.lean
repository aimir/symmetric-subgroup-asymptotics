import SymmetricSubgroupAsymptotics.BinaryCarrierHistoryEnergy

/-! Exact finite-prefix algebra for numerical carrier histories. A cons
history peels its head cost and shifts both tail marks by that same row's
slopes. No sign, row-certificate, group or counting assumptions are used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierHistoryEnergy

@[simp] theorem fin_strictPrefix_zero {t : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Fin (t+1) → M) :
    (∑ a ∈ Finset.univ.filter (fun a => a < (0 : Fin (t+1))), f a) = 0 := by
  simp

/-- The strict prefix below a successor consists of the head and exactly
the predecessor's strict prefix. This is an equality of finite sums. -/
theorem fin_strictPrefix_succ {t : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Fin (t+1) → M) (i : Fin t) :
    (∑ a ∈ Finset.univ.filter (fun a => a < i.succ), f a) =
      f 0 + ∑ a ∈ Finset.univ.filter (fun a => a < i), f a.succ := by
  classical
  have hzero : (0 : Fin (t+1)) < i.succ := Nat.succ_pos i.val
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp only [if_pos hzero, Fin.succ_lt_succ_iff]

theorem fin_cons_strictPrefix_succ {t : ℕ} {M : Type*} [AddCommMonoid M]
    (head : M) (tail : Fin t → M) (i : Fin t) :
    (∑ a ∈ Finset.univ.filter (fun a => a < i.succ), Fin.cons head tail a) =
      head + ∑ a ∈ Finset.univ.filter (fun a => a < i), tail a := by
  simpa only [Fin.cons_zero, Fin.cons_succ] using
    fin_strictPrefix_succ (Fin.cons head tail) i

@[simp] theorem finiteHistoryCost_nil (rows : Fin 0 → JointCapacityRow)
    (x y z : ℝ) : finiteHistoryCost rows x y z = 0 := by
  simp only [finiteHistoryCost, Fin.sum_univ_zero]

/-- Exact recursive form of the previously defined finite numerical cost.
The head's c and g shift every later mark once, preserving their order. -/
theorem finiteHistoryCost_cons {t : ℕ} (r : JointCapacityRow)
    (rows : Fin t → JointCapacityRow) (x y z : ℝ) :
    finiteHistoryCost (Fin.cons r rows) x y z =
      r.cost x y z + finiteHistoryCost rows (x+r.c) (y+r.g) z := by
  have hc (i : Fin t) :
      (∑ a ∈ Finset.univ.filter (fun a => a < i.succ),
        JointCapacityRow.c ((Fin.cons r rows : Fin (t+1) → JointCapacityRow) a)) =
        r.c + ∑ a ∈ Finset.univ.filter (fun a => a < i), (rows a).c := by
    simpa only [Fin.cons_zero, Fin.cons_succ] using
      fin_strictPrefix_succ (fun a : Fin (t+1) =>
        JointCapacityRow.c ((Fin.cons r rows : Fin (t+1) → JointCapacityRow) a)) i
  have hg (i : Fin t) :
      (∑ a ∈ Finset.univ.filter (fun a => a < i.succ),
        JointCapacityRow.g ((Fin.cons r rows : Fin (t+1) → JointCapacityRow) a)) =
        r.g + ∑ a ∈ Finset.univ.filter (fun a => a < i), (rows a).g := by
    simpa only [Fin.cons_zero, Fin.cons_succ] using
      fin_strictPrefix_succ (fun a : Fin (t+1) =>
        JointCapacityRow.g ((Fin.cons r rows : Fin (t+1) → JointCapacityRow) a)) i
  unfold finiteHistoryCost
  rw [Fin.sum_univ_succ]
  simp only [fin_strictPrefix_zero, Fin.cons_zero, Fin.cons_succ, add_zero]
  apply congrArg (fun q : ℝ => r.cost x y z + q)
  apply Finset.sum_congr rfl
  intro i _
  rw [hc i, hg i]
  simp only [add_assoc]

/-- Fin.cases is the same cons tuple, convenient for recursively typed rows. -/
theorem finiteHistoryCost_cases {t : ℕ} (r : JointCapacityRow)
    (rows : Fin t → JointCapacityRow) (x y z : ℝ) :
    finiteHistoryCost (Fin.cases r rows) x y z =
      r.cost x y z + finiteHistoryCost rows (x+r.c) (y+r.g) z :=
  finiteHistoryCost_cons r rows x y z

@[simp] theorem finiteHistoryCost_singleton (r : JointCapacityRow) (x y z : ℝ) :
    finiteHistoryCost (Fin.cons r (Fin.elim0 : Fin 0 → JointCapacityRow)) x y z =
      r.cost x y z := by
  rw [finiteHistoryCost_cons, finiteHistoryCost_nil, add_zero]

end SymmetricSubgroupAsymptotics.BinaryCarrierHistoryEnergy
