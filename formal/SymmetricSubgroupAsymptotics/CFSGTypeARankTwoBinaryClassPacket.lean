import SymmetricSubgroupAsymptotics.SLThreeNonzeroKeyClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoCardTwo
import SymmetricSubgroupAsymptotics.CFSGTypeAOuterGcdCardinality
import Mathlib.Data.Nat.Prime.Int

/-! The nonzero SL3 keys give at most six classes on the SAME original
binary projective model. Its already proved order168 and prime-seven
proper-index bound are retained without recognition or subgroup census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankTwoBinaryClassPacket
open PrimitiveSocleRawStructure

theorem class_card_le_six (q : CFSG.PrimePower) (hq : q.order=2) :
    Nat.card (ConjClasses (CFSG.Models.A 2 q)) ≤ 6 := by
  letI : Finite (Matrix.SpecialLinearGroup (Fin 3) q.Field) :=
    Finite.of_injective (fun A : Matrix.SpecialLinearGroup (Fin 3) q.Field => A.val)
      Subtype.val_injective
  letI : Finite (ConjClasses (Matrix.SpecialLinearGroup (Fin 3) q.Field)) :=
    Finite.of_surjective (@ConjClasses.mk (Matrix.SpecialLinearGroup (Fin 3) q.Field) _)
      ConjClasses.mk_surjective
  let f : Matrix.SpecialLinearGroup (Fin 3) q.Field →* CFSG.Models.A 2 q :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) q.Field))
  have hc : Nat.card (ConjClasses (CFSG.Models.A 2 q)) ≤
      Nat.card (ConjClasses (Matrix.SpecialLinearGroup (Fin 3) q.Field)) :=
    Nat.card_le_card_of_surjective (ConjClasses.map f)
      (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))
  exact hc.trans (by
    simpa only [q.card_field,hq] using SLThreeNonzeroKeyClassBound.class_card_le q.Field)

theorem component_class_card_le_twelve (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.A 2 q)] :
    Nat.card (ConjClasses (CFSG.Models.A 2 q))*
      Nat.card (Outer (CFSG.Models.A 2 q)) ≤ 12 := by
  have hf : q.exponent=1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1:ℕ)≠0)
      (show q.prime^q.exponent=2^1 from hq)).2
  have ho : Nat.card (Outer (CFSG.Models.A 2 q)) ≤ 2 := by
    simpa only [hq,hf] using
      CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd 2 (by decide) q
  exact (Nat.mul_le_mul (class_card_le_six q hq) ho).trans_eq (by decide : 6*2=12)

theorem proper_index_dvd_168 (q : CFSG.PrimePower) (hq : q.order=2)
    (K : Subgroup (CFSG.Models.A 2 q)) : K.index ∣ 168 := by
  simpa only [CFSGTypeARankTwoCardTwo.order_eq_168 q hq] using K.index_dvd_card

end SymmetricSubgroupAsymptotics.CFSGTypeARankTwoBinaryClassPacket
