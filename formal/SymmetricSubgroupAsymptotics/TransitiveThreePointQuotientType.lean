import SymmetricSubgroupAsymptotics.SixPairThreePointNormalTop
import SymmetricSubgroupAsymptotics.TwoBinaryThreeCubicTopTypes
import SymmetricSubgroupAsymptotics.SharpCyclicOrSymmetricThreeEpiEnvelope

/-! Every actual quotient of a transitive three-point top is cyclic or
is the full symmetric-three group. This applies to the literal residual
top of every original denominator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TransitiveThreePointQuotientType
variable (T : Subgroup (Equiv.Perm (Fin 3)))
  [MulAction.IsPretransitive T (Fin 3)]
  {R : Type} [Group R] [Finite R]

 theorem cyclic_or_symmetric (rho : T →* R) (hrho : Function.Surjective rho) :
    IsCyclic R ∨ Nonempty (R ≃* Equiv.Perm (Fin 3)) := by
  by_cases hk : rho.ker=⊥
  · have hi : Function.Injective rho := (MonoidHom.ker_eq_bot_iff rho).mp hk
    let e := MulEquiv.ofBijective rho ⟨hi,hrho⟩
    rcases SixPairThreePointNormalTop.cardinal_cases T with h3 | h6
    · letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      letI : IsCyclic T := isCyclic_of_prime_card h3
      exact Or.inl (isCyclic_of_surjective rho hrho)
    · exact Or.inr ⟨e.symm.trans
        (TwoBinaryThreePermutationCoordinates.symmetricEquivOfCardSix T h6)⟩
  · have hcard : Nat.card R≤2 := by
      have h := SixPairThreePointNormalTop.quotient_card_le_two T rho.ker hk
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective rho hrho).symm.toEquiv).le.trans h
    exact Or.inl (SharpCyclicOrSymmetricThreeEpiEnvelope.cyclic_of_card_le_two hcard)

end SymmetricSubgroupAsymptotics.TransitiveThreePointQuotientType
