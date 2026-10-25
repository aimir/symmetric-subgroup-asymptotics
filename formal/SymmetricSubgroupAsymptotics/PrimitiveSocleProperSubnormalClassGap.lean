import SymmetricSubgroupAsymptotics.ProperSubnormalSimpleExtensionClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.PrimitiveSocleSubnormalClassBound

/-! Proper subnormal groups across the SAME one-factor full socle save
a factor of two in the actual quotient/class product. Cubing saves eight,
which pays one additional power of five from an existing component-product
budget. No comparison to half the class count of the ambient group occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.ProperSubnormalClassGapNumerics

theorem cube_gap_of_twice_bound (a c B : ℕ) (ha : 2 ≤ a)
    (htwo : 2*c ≤ B) (hbudget : B^3 ≤ 5^(a-1)) : c^3 ≤ 5^(a-2) := by
  have hp : 8*c^3 ≤ B^3 := by
    simpa only [mul_pow, show (2 : ℕ)^3=8 by decide] using
      Nat.pow_le_pow_left htwo 3
  have he : 5^(a-1) = 5*5^(a-2) := by
    rw [show a-1=(a-2)+1 by omega, pow_succ']
  have hh := hp.trans hbudget
  rw [he] at hh
  omega

end SymmetricSubgroupAsymptotics.ProperSubnormalClassGapNumerics

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.twice_proper_subnormal_class_card_le_socle_quotient
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    2*Nat.card (ConjClasses H) ≤
      Nat.card (G ⧸ finiteGroupSocle G)*Nat.card (ConjClasses D.Simple) := by
  let e := D.oneFactorEquiv hk
  letI : IsSimpleGroup (finiteGroupSocle G) := e.isSimpleGroup
  have hh := ProperSubnormalSimpleExtensionClassBound.twice_class_card_le_quotient_mul_simple
    (finiteGroupSocle G) H hH hne
  have hc : Nat.card (ConjClasses (finiteGroupSocle G)) ≤
      Nat.card (ConjClasses D.Simple) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact hh.trans (Nat.mul_le_mul_left _ hc)

theorem NonaffineData.twice_proper_subnormal_class_card_le_outer
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    2*Nat.card (ConjClasses H) ≤
      Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple) := by
  have hquot : Nat.card (G ⧸ finiteGroupSocle G) ≤ Nat.card (Outer D.Simple) := by
    have hh := Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective
    have hw : Nat.card (OuterWreathPermutationCompression.Wreath
        (Outer D.Simple) D.factorCount) =
        Nat.card (Outer D.Simple)^D.factorCount*D.factorCount.factorial := by
      rw [PermutationalWreathProduct.natCard_eq, Nat.card_fin, Nat.card_perm, Nat.card_fin]
    rw [hw, hk, pow_one, Nat.factorial_one, mul_one] at hh
    exact hh
  exact (D.twice_proper_subnormal_class_card_le_socle_quotient hk H hH hne).trans
    ((Nat.mul_le_mul_right _ hquot).trans_eq (Nat.mul_comm _ _))

theorem NonaffineData.proper_subnormal_class_cube_le_of_factor_one
    (D : NonaffineData G X) (hk : D.factorCount=1) (hdegree : 2 ≤ Nat.card X)
    (hbase : (Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple))^3 ≤
      5^(Nat.card X-1))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) :=
  ProperSubnormalClassGapNumerics.cube_gap_of_twice_bound _ _ _ hdegree
    (D.twice_proper_subnormal_class_card_le_outer hk H hH hne) hbase

theorem NonaffineData.proper_subnormal_class_cube_le_of_factor_one_order
    (D : NonaffineData G X) (hk : D.factorCount=1) (hdegree : 2 ≤ Nat.card X)
    (hbase : (Nat.card D.Simple*Nat.card (Outer D.Simple))^3 ≤ 5^(Nat.card X-1))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  have hc : Nat.card (ConjClasses D.Simple) ≤ Nat.card D.Simple :=
    Nat.card_le_card_of_surjective (@ConjClasses.mk D.Simple _) ConjClasses.mk_surjective
  apply D.proper_subnormal_class_cube_le_of_factor_one hk hdegree _ H hH hne
  exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hc) 3).trans hbase

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
