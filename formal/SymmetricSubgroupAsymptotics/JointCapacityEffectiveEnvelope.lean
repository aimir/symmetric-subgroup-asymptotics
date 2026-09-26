import SymmetricSubgroupAsymptotics.JointCapacityRowEnvelope

/-! The coupled polygon only sees min(n,k+m). This permits domination
by a displayed row whose order entry is smaller than the original order,
without changing that original order or forgetting the joint constraint.
The support comparison holds for arbitrary real marks. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem jointCapacitySupport_mono_effective
    {k n m K N M : ℕ} {x y X Y : ℝ}
    (hk : k ≤ K) (hn : min n (k+m) ≤ N) (hm : m ≤ M)
    (hx : x ≤ X) (hy : y ≤ Y) :
    jointCapacitySupport k n m x y ≤ jointCapacitySupport K N M X Y := by
  apply jointCapacitySupport_le
  intro δ ε hδ hε hjoint
  have heff : δ + ε ≤ min n (k+m) := le_min hjoint (Nat.add_le_add hδ hε)
  exact (add_le_add
    (mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg δ))
    (mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg ε))).trans
      (le_jointCapacitySupport X Y (hδ.trans hk) (hε.trans hm) (heff.trans hn))

namespace JointCapacityRow

/-- This compares the full feasible polygon and all remaining row fields.
It makes no assertion that the literal subgroup order is bounded. -/
structure EffectivelyBoundedBy (r s : JointCapacityRow) : Prop where
  head : r.k ≤ s.k
  effectiveOrder : min r.n (r.k+r.m) ≤ s.n
  derivedHead : r.m ≤ s.m
  radicalHead : r.a₂ ≤ s.a₂
  center : r.c ≤ s.c
  derived : r.g ≤ s.g

theorem BoundedBy.effective {r s : JointCapacityRow} (h : r.BoundedBy s) :
    r.EffectivelyBoundedBy s :=
  ⟨h.head, (min_le_left _ _).trans h.order, h.derivedHead,
    h.radicalHead, h.center, h.derived⟩

theorem EffectivelyBoundedBy.refl (r : JointCapacityRow) : r.EffectivelyBoundedBy r :=
  ⟨le_rfl, min_le_left _ _, le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem EffectivelyBoundedBy.trans {r s t : JointCapacityRow}
    (h : r.EffectivelyBoundedBy s) (j : s.EffectivelyBoundedBy t) :
    r.EffectivelyBoundedBy t := by
  refine ⟨h.head.trans j.head, ?_, h.derivedHead.trans j.derivedHead,
    h.radicalHead.trans j.radicalHead, h.center.trans j.center, h.derived.trans j.derived⟩
  exact (le_min h.effectiveOrder
    ((min_le_right _ _).trans (Nat.add_le_add h.head h.derivedHead))).trans j.effectiveOrder

theorem EffectivelyBoundedBy.second {r s : JointCapacityRow}
    (h : r.EffectivelyBoundedBy s) : max r.m r.a₂ ≤ max s.m s.a₂ :=
  max_le_max h.derivedHead h.radicalHead

theorem directedSupport_mono_effective {r s R S : JointCapacityRow}
    (hr : r.EffectivelyBoundedBy R) (hs : s.EffectivelyBoundedBy S) :
    directedSupport r s ≤ directedSupport R S :=
  jointCapacitySupport_mono_effective hs.head hs.effectiveOrder hs.derivedHead
    hr.center hr.derived

theorem symmetricSupport_mono_effective {r s R S : JointCapacityRow}
    (hr : r.EffectivelyBoundedBy R) (hs : s.EffectivelyBoundedBy S) :
    symmetricSupport r s ≤ symmetricSupport R S :=
  max_le_max (directedSupport_mono_effective hr hs) (directedSupport_mono_effective hs hr)

theorem cost_mono_effective {r s : JointCapacityRow} (h : r.EffectivelyBoundedBy s)
    (x y z : ℝ) (hz : 0 ≤ z) : r.cost x y z ≤ s.cost x y z := by
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hz
    exact add_le_add (Nat.cast_le.mpr h.head) (Nat.cast_le.mpr h.second)
  · exact jointCapacitySupport_mono_effective h.head h.effectiveOrder h.derivedHead
      le_rfl le_rfl

end JointCapacityRow
end SymmetricSubgroupAsymptotics
