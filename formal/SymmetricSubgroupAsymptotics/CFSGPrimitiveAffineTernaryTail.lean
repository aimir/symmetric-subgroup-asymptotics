import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineTernaryPrimeTail
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineTernaryTailNumerics

/-! All actual affine relative-three heads in degree≥34 are strictly below
3/20 of their degree. No ordinary normal-generator inequality is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
open CFSGPrimitiveTernaryTailNumerics CFSGPrimitiveAffineTernaryTailNumerics

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem relativeThreeHead_strict_tail (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (hf : 34 ≤ Nat.card X)
    (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) < 3*Nat.card X := by
  by_cases hs : Nat.card X < 1024
  · obtain ⟨p,d,hp',hd,he,hdiv,hne⟩ := P.exists_prime_dimension_order_divisor hp
    by_cases hd1 : d=1
    · have hprime : (Nat.card X).Prime := by simpa only [he,hd1,pow_one] using hp'
      exact P.relativeThreeHead_strict_prime_tail hp hprime hf N
    · have hv := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hne).2 hdiv 3
      have hh := P.relativeHead_add_degreeFactorization_budget hp 3 (by omega) N
      have hb := fullAffineOrder_strict_tail (p := p) (d := d) hp' (by omega) (by rwa [←he])
        (by rwa [←he])
      rw [←he] at hb
      omega
  · have hh := P.relativeThreeHead_le_logSquare hp N
    have ht := quadratic_log_tail (show 1024 ≤ Nat.card X by omega)
    nlinarith

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
