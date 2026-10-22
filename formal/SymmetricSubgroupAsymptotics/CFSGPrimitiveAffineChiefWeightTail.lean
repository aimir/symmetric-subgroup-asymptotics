import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineChiefWeightPrimeTail
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineChiefWeightTailNumerics

/-! The actual affine three-tenths chief-weight tail, retaining every
original chief series and the actual full-affine order divisor. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
open CFSGPrimitiveTernaryTailNumerics CFSGPrimitiveAffineChiefWeightTailNumerics

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem chiefThreeWeight_threeTenths_tail (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (hf : 45 ≤ Nat.card X)
    (c : ActualChiefSeries G) :
    10*actualChiefSeriesTernaryWeight c ≤ 3*Nat.card X := by
  by_cases hs : Nat.card X < 1024
  · obtain ⟨p,d,hp',hd,he,hdiv,hne⟩ := P.exists_prime_dimension_order_divisor hp
    by_cases hd1 : d=1
    · have hprime : (Nat.card X).Prime := by simpa only [he,hd1,pow_one] using hp'
      have hh := P.chiefThreeWeight_strict_prime_tail hp hprime (by omega) c
      omega
    · have hv := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hne).2 hdiv 3
      have hh := actualChiefSeriesTernaryWeight_le_order c
      have hb := fullAffineOrder_threeTenths_tail (p := p) (d := d) hp' (by omega)
        (by rwa [←he]) (by rwa [←he])
      rw [←he] at hb
      omega
  · have hh := P.chiefThreeWeight_le_logSquare hp c
    have ht := quadratic_log_tail (show 1024 ≤ Nat.card X by omega)
    nlinarith

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
