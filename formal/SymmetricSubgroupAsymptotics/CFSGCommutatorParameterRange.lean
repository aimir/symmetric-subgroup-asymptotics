import SymmetricSubgroupAsymptotics.CFSGRootParameterAutomorphism

/-! A coefficient-one commutator parametrization makes the third root
image intrinsic to the first two. No finiteness or injectivity is needed:
every third-root parameter is obtained by taking the second parameter 1. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGCommutatorParameterRange
variable {K G : Type*} [Field K] [Group G]

theorem commutator_range_map
    (u v w : Multiplicative K →* G)
    (hcomm : ∀ a b : K,
      u (Multiplicative.ofAdd a) * v (Multiplicative.ofAdd b) *
        (u (Multiplicative.ofAdd a))⁻¹ * (v (Multiplicative.ofAdd b))⁻¹ =
          w (Multiplicative.ofAdd (a * b)))
    (f : G →* G) (hfu : u.range.map f = u.range)
    (hfv : v.range.map f = v.range) : w.range.map f = w.range := by
  apply le_antisymm
  · rintro y ⟨x, ⟨a, rfl⟩, rfl⟩
    have hua : f (u a) ∈ u.range := by
      rw [← hfu]
      exact ⟨u a, ⟨a, rfl⟩, rfl⟩
    have hvb : f (v (Multiplicative.ofAdd (1 : K))) ∈ v.range := by
      rw [← hfv]
      exact ⟨v (Multiplicative.ofAdd 1), ⟨Multiplicative.ofAdd 1, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := hua
    obtain ⟨c, hc⟩ := hvb
    refine ⟨Multiplicative.ofAdd (b.toAdd * c.toAdd), ?_⟩
    calc
      w (Multiplicative.ofAdd (b.toAdd * c.toAdd)) =
          u b * v c * (u b)⁻¹ * (v c)⁻¹ := (hcomm b.toAdd c.toAdd).symm
      _ = f (u a * v (Multiplicative.ofAdd 1) *
          (u a)⁻¹ * (v (Multiplicative.ofAdd 1))⁻¹) := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hb, hc]
      _ = f (w a) := congrArg f (by simpa only [mul_one] using hcomm a.toAdd 1)
  · rintro y ⟨a, rfl⟩
    have hua : u a ∈ u.range.map f := by
      rw [hfu]
      exact ⟨a, rfl⟩
    have hvb : v (Multiplicative.ofAdd (1 : K)) ∈ v.range.map f := by
      rw [hfv]
      exact ⟨Multiplicative.ofAdd 1, rfl⟩
    rcases hua with ⟨x, ⟨b, rfl⟩, hb⟩
    rcases hvb with ⟨x, ⟨c, rfl⟩, hc⟩
    refine ⟨w (Multiplicative.ofAdd (b.toAdd * c.toAdd)), ⟨_, rfl⟩, ?_⟩
    calc
      f (w (Multiplicative.ofAdd (b.toAdd * c.toAdd))) =
          f (u b * v c * (u b)⁻¹ * (v c)⁻¹) :=
            congrArg f (hcomm b.toAdd c.toAdd).symm
      _ = u a * v (Multiplicative.ofAdd 1) *
          (u a)⁻¹ * (v (Multiplicative.ofAdd 1))⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hb, hc]
      _ = w a := by simpa only [mul_one] using hcomm a.toAdd 1

end SymmetricSubgroupAsymptotics.CFSGCommutatorParameterRange
