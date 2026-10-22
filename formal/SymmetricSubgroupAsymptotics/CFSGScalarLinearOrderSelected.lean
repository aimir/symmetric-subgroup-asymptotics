import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms
import SymmetricSubgroupAsymptotics.CFSGChiefPrimeFactorBudget
import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor

/-! Exact order accounting for a field-automorphism action with a faithful
linear kernel. The selected binary dimension-six scalar degrees have
prime-factor budgets thirteen, eight and five. No subgroup census is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGScalarLinearOrderSelected

theorem card_dvd_linear_mul_fieldAut
    {G K W : Type} [Group G] [Finite G] [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (theta : G →* (K ≃+* K))
    (sigma : Representation K theta.ker W) (hf : Function.Injective sigma) :
    Nat.card G ∣ fullLinearOrder (Nat.card K) (Module.finrank K W) *
      Nat.card (K ≃+* K) := by
  let b := Module.finBasis K W
  let phi : theta.ker →* Matrix.GeneralLinearGroup (Fin (Module.finrank K W)) K :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp sigma.asGroupHom
  have hphi : Function.Injective phi := by
    intro g h he
    apply hf
    exact congrArg Units.val ((Matrix.GeneralLinearGroup.toLin' b).symm.injective he)
  have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin (Module.finrank K W)) K) =
      fullLinearOrder (Nat.card K) (Module.finrank K W) := by
    letI : Fintype K := Fintype.ofFinite K
    rw [Matrix.card_GL_field]
    simp only [fullLinearOrder, Nat.card_eq_fintype_card]
  have hker : Nat.card theta.ker ∣
      fullLinearOrder (Nat.card K) (Module.finrank K W) :=
    hgl ▸ Subgroup.card_dvd_of_injective phi hphi
  have hrange : Nat.card theta.range ∣ Nat.card (K ≃+* K) :=
    Subgroup.card_subgroup_dvd_card theta.range
  have he : Nat.card G = Nat.card theta.ker * Nat.card theta.range := by
    rw [← Subgroup.index_ker theta]
    exact theta.ker.card_mul_index.symm
  rw [he]
  exact Nat.mul_dvd_mul hker hrange

theorem selected_scalar_omega :
    ArithmeticFunction.cardFactors (fullLinearOrder 4 3 * 2) = 13 ∧
    ArithmeticFunction.cardFactors (fullLinearOrder 8 2 * 3) = 8 ∧
    ArithmeticFunction.cardFactors (fullLinearOrder 64 1 * 6) = 5 := by
  unfold fullLinearOrder
  decide +kernel

theorem trace_le_fourteen_of_scalar_kernel
    {G K W : Type} [Group G] [Finite G] [Field K] [Finite K]
    [Algebra (ZMod 2) K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (theta : G →* (K ≃+* K))
    (sigma : Representation K theta.ker W) (hf : Function.Injective sigma)
    (hd : (Module.finrank (ZMod 2) K = 2 ∧ Module.finrank K W = 3) ∨
      (Module.finrank (ZMod 2) K = 3 ∧ Module.finrank K W = 2) ∨
      (Module.finrank (ZMod 2) K = 6 ∧ Module.finrank K W = 1))
    (T : FixedTargetCompositionTrace G) : T.envelope.abelianLength ≤ 14 := by
  have hdiv := card_dvd_linear_mul_fieldAut theta sigma hf
  have hK := FiniteField.pow_finrank_eq_natCard 2 K
  rw [CFSGFiniteFieldAutomorphisms.card_ringAut K 2, ← hK] at hdiv
  rcases hd with ⟨he, hm⟩ | ⟨he, hm⟩ | ⟨he, hm⟩
  · rw [he, hm] at hdiv
    have hh := CFSGChiefPrimeFactorBudget.cardFactors_mono
      (by decide : fullLinearOrder (2^2) 3 * 2 ≠ 0) hdiv
    rw [show 2^2 = 4 by decide, selected_scalar_omega.1] at hh
    have ht := CFSGChiefPrimeFactorBudget.trace_charge_le_cardFactors T
    omega
  · rw [he, hm] at hdiv
    have hh := CFSGChiefPrimeFactorBudget.cardFactors_mono
      (by decide : fullLinearOrder (2^3) 2 * 3 ≠ 0) hdiv
    rw [show 2^3 = 8 by decide, selected_scalar_omega.2.1] at hh
    have ht := CFSGChiefPrimeFactorBudget.trace_charge_le_cardFactors T
    omega
  · rw [he, hm] at hdiv
    have hh := CFSGChiefPrimeFactorBudget.cardFactors_mono
      (by decide : fullLinearOrder (2^6) 1 * 6 ≠ 0) hdiv
    rw [show 2^6 = 64 by decide, selected_scalar_omega.2.2] at hh
    have ht := CFSGChiefPrimeFactorBudget.trace_charge_le_cardFactors T
    omega

end SymmetricSubgroupAsymptotics.CFSGScalarLinearOrderSelected
