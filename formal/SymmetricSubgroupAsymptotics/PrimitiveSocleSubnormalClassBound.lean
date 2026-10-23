import SymmetricSubgroupAsymptotics.SubnormalSemisimpleClassExtension
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScott

/-! Actual subnormal subgroups of the original nonaffine group are
counted across the original full socle. The kernel intersection consists
of whole simple coordinates; the quotient is the original outer-wreath
image. No bound for arbitrary subgroups of the simple factor is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_card_le_socle_quotient
    (D : NonaffineData G X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses D.Simple)^D.factorCount *
      Nat.card (G ⧸ finiteGroupSocle G) := by
  let N := finiteGroupSocle G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let a : q.ker ≃* N := MulEquiv.subgroupCongr (QuotientGroup.ker_mk' N)
  let e := a.trans D.socleEquiv
  have hh := SubnormalSemisimpleClassExtension.subnormal_class_card_le_kernel_mul_card
    q D.factorCount (fun _ => D.Simple) e H hH
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh

theorem NonaffineData.subnormal_class_card_le_outer_wreath
    (D : NonaffineData G X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ≤
      (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple))^D.factorCount *
        D.factorCount.factorial := by
  have hquot : Nat.card (G ⧸ finiteGroupSocle G) ≤
      Nat.card (Outer D.Simple)^D.factorCount * D.factorCount.factorial := by
    have hh := Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective
    have he : Nat.card (OuterWreathPermutationCompression.Wreath
        (Outer D.Simple) D.factorCount)=
        Nat.card (Outer D.Simple)^D.factorCount * D.factorCount.factorial := by
      rw [PermutationalWreathProduct.natCard_eq,Nat.card_fin,Nat.card_perm,Nat.card_fin]
    exact hh.trans_eq he
  calc
    Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses D.Simple)^D.factorCount *
        Nat.card (G ⧸ finiteGroupSocle G) :=
      D.subnormal_class_card_le_socle_quotient H hH
    _ ≤ Nat.card (ConjClasses D.Simple)^D.factorCount *
        (Nat.card (Outer D.Simple)^D.factorCount * D.factorCount.factorial) :=
      Nat.mul_le_mul_left _ hquot
    _ = (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple))^D.factorCount *
        D.factorCount.factorial := by rw [mul_pow]; exact (Nat.mul_assoc _ _ _).symm

theorem NonaffineData.subnormal_class_card_le_of_factor_one
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple) := by
  have hh := D.subnormal_class_card_le_outer_wreath H hH
  simpa only [hk,pow_one,Nat.factorial_one,mul_one] using hh

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
