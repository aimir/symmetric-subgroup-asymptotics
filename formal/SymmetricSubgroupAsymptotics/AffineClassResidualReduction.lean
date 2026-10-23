import SymmetricSubgroupAsymptotics.AffineProfileSubgroupClassBound
import SymmetricSubgroupAsymptotics.PrimeDegreeAffineSubgroupClassBound
import SymmetricSubgroupAsymptotics.SmallAffinePrimePowerDegrees

/-! Every actual affine-profile subgroup either satisfies the GM cube or
has one of ten explicitly retained ambient degrees. The finite residual
is exposed, rather than supplied as a classification or class callback. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AffineClassResidualReduction

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_cube_or_residual (x : X) (hn : 4 ≤ Nat.card X)
    (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨
      SmallAffinePrimePowerDegrees.ResidualDegree (Nat.card X) := by
  by_cases hlarge : 64 ≤ Nat.card X
  · exact Or.inl (AffineProfileSubgroupClassBound.subgroup_class_cube_le_garonziMaroti
      P x hlarge H)
  by_cases hprime : 11 ≤ Nat.card X ∧ Nat.Prime (Nat.card X)
  · exact Or.inl (PrimeDegreeAffineSubgroupClassBound.subgroup_class_cube_le_garonziMaroti
      P x hprime.2 hprime.1 H)
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  obtain ⟨e,he⟩ := P.V_pgroup.exists_card_eq
  have heq : Nat.card X=P.p^e := (P.card_eq x).symm.trans he
  exact Or.inr (SmallAffinePrimePowerDegrees.residual_of_small_prime_power
    P.p e (Nat.card X) P.p_prime heq hn (by omega) hprime)

end SymmetricSubgroupAsymptotics.AffineClassResidualReduction
