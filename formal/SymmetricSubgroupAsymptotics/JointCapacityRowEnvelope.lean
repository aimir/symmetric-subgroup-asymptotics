import SymmetricSubgroupAsymptotics.JointCapacityHistory

/-! Safe upper envelopes for actual coupled-capacity rows. Enlarging the
feasible polygon is valid even for negative first marks. Quotient slopes
are enlarged only in their stated direction, never subtracted from a bound.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem jointCapacitySupport_mono
    {k n m K N M : ℕ} {x y X Y : ℝ}
    (hk : k ≤ K) (hn : n ≤ N) (hm : m ≤ M) (hx : x ≤ X) (hy : y ≤ Y) :
    jointCapacitySupport k n m x y ≤ jointCapacitySupport K N M X Y := by
  apply jointCapacitySupport_le
  intro δ ε hδ hε hjoint
  exact (add_le_add
    (mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg δ))
    (mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg ε))).trans
      (le_jointCapacitySupport X Y (hδ.trans hk) (hε.trans hm) (hjoint.trans hn))

namespace JointCapacityRow

/-- Every coordinate is bounded on the same original row. This is only
an invariant envelope, not a counting or owner-acceptance hypothesis. -/
structure BoundedBy (r s : JointCapacityRow) : Prop where
  head : r.k ≤ s.k
  order : r.n ≤ s.n
  derivedHead : r.m ≤ s.m
  radicalHead : r.a₂ ≤ s.a₂
  center : r.c ≤ s.c
  derived : r.g ≤ s.g

theorem BoundedBy.second {r s : JointCapacityRow} (h : BoundedBy r s) :
    max r.m r.a₂ ≤ max s.m s.a₂ := max_le_max h.derivedHead h.radicalHead

theorem directedSupport_mono {r s R S : JointCapacityRow}
    (hr : BoundedBy r R) (hs : BoundedBy s S) :
    directedSupport r s ≤ directedSupport R S :=
  jointCapacitySupport_mono hs.head hs.order hs.derivedHead hr.center hr.derived

theorem symmetricSupport_mono {r s R S : JointCapacityRow}
    (hr : BoundedBy r R) (hs : BoundedBy s S) :
    symmetricSupport r s ≤ symmetricSupport R S :=
  max_le_max (directedSupport_mono hr hs) (directedSupport_mono hs hr)

/-- Upper capacities can replace exact capacities in a marked cost. The
terminal multiplier must remain nonnegative; the first mark is arbitrary. -/
theorem cost_mono {r s : JointCapacityRow} (h : BoundedBy r s)
    (x y z : ℝ) (hz : 0 ≤ z) : r.cost x y z ≤ s.cost x y z := by
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hz
    exact add_le_add (Nat.cast_le.mpr h.head) (Nat.cast_le.mpr h.second)
  · exact jointCapacitySupport_mono h.head h.order h.derivedHead le_rfl le_rfl

end JointCapacityRow
end SymmetricSubgroupAsymptotics
