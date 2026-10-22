import SymmetricSubgroupAsymptotics.CFSGCommutatorParameterRange

/-! A coefficient-unit mixed commutator determines the opposite-root
parameter. This elementary group lemma will be applied to actual Weyl
transports of the original positive A2 relation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCommutatorParameterRigidity
variable {K G : Type*} [Field K] [Group G]

theorem fixed_parameter_of_mixed_commutator (u v w : K → G)
    (hu : Function.Injective u) (c : K) (hc : c ≠ 0)
    (hcomm : ∀ a b, v a * w b * (v a)⁻¹ * (w b)⁻¹ = u (c * (a * b)))
    (f : G →* G) (hfu : ∀ a, f (u a) = u a) (hfw : ∀ b, f (w b) = w b)
    (hfv : ∀ a, ∃ b, f (v a) = v b) : ∀ a, f (v a) = v a := by
  intro a
  obtain ⟨b, hb⟩ := hfv a
  have he := congrArg f (hcomm a 1)
  simp only [map_mul, map_inv, hb, hfw, hfu] at he
  rw [hcomm, mul_one, mul_one] at he
  have hba : b = a := mul_left_cancel₀ hc (hu he)
  simpa only [hba] using hb

end SymmetricSubgroupAsymptotics.CFSGCommutatorParameterRigidity
