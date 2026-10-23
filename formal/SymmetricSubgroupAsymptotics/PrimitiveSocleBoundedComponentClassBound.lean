import SymmetricSubgroupAsymptotics.PrimitiveSoclePowerDegreeOrderBound
import SymmetricSubgroupAsymptotics.BoundedComponentSocleClassNumerics
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex

/-! Bounded-dimensional simple components pay the full large primitive
class cube, retaining the original socle, quotient embedding and number
of factors. The per-component index/order input is explicit here and is
discharged by each concrete-family consumer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.card_le_simple_outer_wreath (D : NonaffineData G X) :
    Nat.card G ≤ (Nat.card D.Simple*Nat.card (Outer D.Simple))^D.factorCount *
      D.factorCount.factorial := by
  let s := Nat.card D.Simple
  let o := Nat.card (Outer D.Simple)
  let k := D.factorCount
  have hsocle : Nat.card (finiteGroupSocle G)=s^k := by
    rw [Nat.card_congr D.socleEquiv.toEquiv, Nat.card_fun, Nat.card_fin]
  have hquotient : Nat.card (G⧸finiteGroupSocle G) ≤ o^k*k.factorial := by
    have h := Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective
    have he : Nat.card (OuterWreathPermutationCompression.Wreath (Outer D.Simple) k)=
        o^k*k.factorial := by
      rw [PermutationalWreathProduct.natCard_eq, Nat.card_fin, Nat.card_perm, Nat.card_fin]
    exact h.trans_eq he
  calc
    Nat.card G = Nat.card (G⧸finiteGroupSocle G)*Nat.card (finiteGroupSocle G) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (finiteGroupSocle G)
    _ ≤ (o^k*k.factorial)*s^k := Nat.mul_le_mul hquotient hsocle.le
    _ = (s*o)^k*k.factorial := by rw [mul_pow]; ring

theorem NonaffineData.subgroup_class_cube_le_of_bounded_component
    (D : NonaffineData G X) (K : Subgroup D.Simple) (hK : K≠⊤)
    (hdegree : Nat.card X=K.index^D.factorCount)
    (hcomponent : Nat.card D.Simple*Nat.card (Outer D.Simple) ≤ K.index^66)
    (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hm : 5 ≤ K.index := nonabelianSimple_proper_index_five_le
    (fun hc => D.noncommutative (isMulCommutative_iff.mpr hc)) K hK
  have hcard : Nat.card (ConjClasses H) ≤
      (K.index^66)^D.factorCount*D.factorCount.factorial := by
    apply (Nat.card_le_card_of_surjective (@ConjClasses.mk H _)
      ConjClasses.mk_surjective).trans
    apply H.card_le_card_group.trans
    exact D.card_le_simple_outer_wreath.trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcomponent _))
  rw [hdegree]
  exact (Nat.pow_le_pow_left hcard 3).trans
    (BoundedComponentSocleClassNumerics.component_cube_le_garonziMaroti
      K.index D.factorCount hm D.factorCount_pos (by rwa [←hdegree]))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
