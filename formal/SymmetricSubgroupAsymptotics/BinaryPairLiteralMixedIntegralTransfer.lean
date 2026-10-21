import SymmetricSubgroupAsymptotics.BinaryPairIntegralMixedTopBound
import SymmetricSubgroupAsymptotics.BinaryPairKernelRadicalDerived

/-! A small literal top-displacement certificate bounds the integral
relative quotient of the SAME original normal. The original kernel may
be larger than the checked test space, so correlations are preserved. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

/-- Only a specified test subspace is needed; the entire original pair
kernel remains in the source and in its integral commutator intersection. -/
theorem integral_order_le_two_mul_top_of_literal_mixed_capacity
    (H : Subgroup (Equiv.Perm (Fin w))) (hH : F.top.range = H)
    (K R : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hK : K ≤ F.kernelSpace)
    (E L : Subgroup U) [E.Normal]
    (hR : F.ambientAxis L = R)
    (hL : L ≤ ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker)
    (m : ℕ)
    (hcapacity : Nat.card {t : H // ∀ v, v ∈ K →
      ((binaryPermutationRepresentation w).comp H.subtype) t v - v ∈ R} ≤ m)
    (himage : m < Nat.card (E.map F.top.rangeRestrict))
    (hA : Nat.card (E ⊓ F.top.ker : Subgroup U) ≤ 4 * Nat.card L) :
    normalIntegralCoinvariantOrder E ≤
      2 * normalIntegralCoinvariantOrder (E.map F.top.rangeRestrict) := by
  let e : H ≃* F.top.range := MulEquiv.subgroupCongr hH.symm
  have he (t : H) (v : Fin w → ZMod 2) :
      ((binaryPermutationRepresentation w).comp H.subtype) t v =
        F.coordinateTopAction (e t) v := rfl
  let j : {t : F.top.range // ∀ v, v ∈ F.kernelSpace →
      F.coordinateTopAction t v - v ∈ F.ambientAxis L} →
      {t : H // ∀ v, v ∈ K →
        ((binaryPermutationRepresentation w).comp H.subtype) t v - v ∈ R} := fun t =>
    ⟨e.symm t.val, by
      intro v hv
      rw [he, e.apply_symm_apply, ← hR]
      exact t.property v (hK hv)⟩
  have hj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg Subtype.val h
  have hb := (Nat.card_le_card_of_injective j hj).trans hcapacity
  exact F.integral_order_le_two_mul_top_of_displacement_gap E L hL
    (lt_of_le_of_lt hb himage) hA

end SymmetricSubgroupAsymptotics.BinaryPairFrame
