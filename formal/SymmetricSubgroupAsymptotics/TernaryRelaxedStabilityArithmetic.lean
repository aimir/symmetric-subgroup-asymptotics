import SymmetricSubgroupAsymptotics.TernaryStabilityArithmetic

/-! The sole needed relaxation of the transitive head envelope is value2
at degree10. The actual induced width there is2, so the original scalar
recurrence still closes at every composite degree. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

def ternaryRelaxedStabilityBound (w : ℕ) : ℕ :=
  if w=10 then 2 else ternaryStabilityBound w

theorem ternaryIndexWidth_ten : ternaryIndexWidth 10=2 := by decide +kernel

theorem ternaryStability_le_relaxed (w : ℕ) :
    ternaryStabilityBound w≤ternaryRelaxedStabilityBound w := by
  by_cases h : w=10
  · subst w
    norm_num [ternaryRelaxedStabilityBound,ternaryStabilityBound]
  · simp only [ternaryRelaxedStabilityBound,if_neg h,le_refl]

theorem ternaryRelaxedStability_scalar (r s : ℕ) (hr : 2≤r) (hs : 2≤s)
    (h18 : r*s≠18) :
    (r/3)*ternaryIndexWidth s+ternaryRelaxedStabilityBound s≤
      ternaryRelaxedStabilityBound (r*s) := by
  by_cases h10 : s=10
  · subst s
    rw [ternaryIndexWidth_ten]
    have hsmall : ternaryRelaxedStabilityBound 10=2 := by rfl
    rw [hsmall]
    apply le_trans ?_ (ternaryStability_le_relaxed (r*10))
    apply le_trans ?_ (ternaryStability_base_le (r*10) h18)
    apply (Nat.le_div_iff_mul_le (by decide : 0<27)).mpr
    have hv := Nat.div_mul_le_self r 3
    nlinarith
  · have h := ternaryStability_scalar r s hr hs h18
    have hh : (r/3)*ternaryIndexWidth s+ternaryRelaxedStabilityBound s≤
        ternaryStabilityBound (r*s) := by
      simpa only [ternaryRelaxedStabilityBound,if_neg h10] using h
    exact hh.trans (ternaryStability_le_relaxed (r*s))

end SymmetricSubgroupAsymptotics
