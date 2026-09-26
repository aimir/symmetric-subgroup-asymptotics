import SymmetricSubgroupAsymptotics.JointCapacityHistory

/-! A finite scalar upper bound for the exact coupled-capacity support.
It combines the rectangle bound with a dual bound for the joint order
constraint. Nonnegative slopes are explicit; arbitrary marked costs are
not replaced by this nonnegative-slope specialization. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

def jointCapacityPolygonBudget (k n m : ℕ) (x y : ℝ) : ℝ :=
  min (x * k + y * m)
    (max (x - y) 0 * k + max (y - x) 0 * m + min x y * n)

theorem jointCapacitySupport_le_polygonBudget (k n m : ℕ) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    jointCapacitySupport k n m x y ≤ jointCapacityPolygonBudget k n m x y := by
  apply jointCapacitySupport_le
  intro δ ε hδ hε hjoint
  have hd : (δ : ℝ) ≤ k := Nat.cast_le.mpr hδ
  have he : (ε : ℝ) ≤ m := Nat.cast_le.mpr hε
  have hn : (δ : ℝ) + ε ≤ n := by exact_mod_cast hjoint
  apply le_min
  · exact add_le_add (mul_le_mul_of_nonneg_left hd hx)
      (mul_le_mul_of_nonneg_left he hy)
  · rcases le_total x y with hxy | hyx
    · rw [max_eq_right (sub_nonpos.mpr hxy), max_eq_left (sub_nonneg.mpr hxy),
        min_eq_left hxy]
      calc
        x * (δ : ℝ) + y * ε = (y - x) * (ε : ℝ) + x * ((δ : ℝ) + ε) := by ring
        _ ≤ (y - x) * (m : ℝ) + x * n := add_le_add
          (mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hxy))
          (mul_le_mul_of_nonneg_left hn hx)
        _ = _ := by ring
    · rw [max_eq_left (sub_nonneg.mpr hyx), max_eq_right (sub_nonpos.mpr hyx),
        min_eq_right hyx]
      calc
        x * (δ : ℝ) + y * ε = (x - y) * (δ : ℝ) + y * ((δ : ℝ) + ε) := by ring
        _ ≤ (x - y) * (k : ℝ) + y * n := add_le_add
          (mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hyx))
          (mul_le_mul_of_nonneg_left hn hy)
        _ = _ := by ring

namespace JointCapacityRow

def polygonPairBudget (r s : JointCapacityRow) : ℝ :=
  max (jointCapacityPolygonBudget s.k s.n s.m r.c r.g)
    (jointCapacityPolygonBudget r.k r.n r.m s.c s.g)

theorem symmetricSupport_le_polygonPairBudget (r s : JointCapacityRow)
    (hrc : 0 ≤ r.c) (hrg : 0 ≤ r.g) (hsc : 0 ≤ s.c) (hsg : 0 ≤ s.g) :
    r.symmetricSupport s ≤ r.polygonPairBudget s :=
  max_le_max (jointCapacitySupport_le_polygonBudget s.k s.n s.m r.c r.g hrc hrg)
    (jointCapacitySupport_le_polygonBudget r.k r.n r.m s.c s.g hsc hsg)

end JointCapacityRow
end SymmetricSubgroupAsymptotics
