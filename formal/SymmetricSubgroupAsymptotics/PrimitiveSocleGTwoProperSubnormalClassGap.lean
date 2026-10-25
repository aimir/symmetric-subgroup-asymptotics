import SymmetricSubgroupAsymptotics.PrimitiveSocleAllFactorProperClassGap
import SymmetricSubgroupAsymptotics.CFSGGTwoProperIndexComponentCube
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Every actual original G2 simple component pays the proper-subnormal
extra class exponent, with all socle factors and both degree forms. The
actual q^12 source lower bound supplies the power-form threshold. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_gTwo_component
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hs : q.order ≠ 2)
    (e : D.Simple ≃* CFSG.Models.G2 q) (hdegree : 2 ≤ Nat.card X)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative (CFSG.Models.G2 q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hq : 3 ≤ q.order := by
    have ht : 2 ≤ q.order :=
      q.prime_isPrime.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.prime)
    omega
  have hlarge : 1024 ≤ Nat.card D.Simple := by
    rw [Nat.card_congr e.toEquiv]
    have hc := CFSGGTwoD4GeckOriginalProjection.original_order_lower q.Field
    rw [q.card_field] at hc
    exact ((by decide : 1024 ≤ 3^12).trans (Nat.pow_le_pow_left hq 12)).trans hc
  apply D.proper_subnormal_class_cube_le_of_order_index_budget hdegree hlarge _ H hH hne
  intro K hK
  have hmap : K.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  rw [Nat.card_congr e.toEquiv, outer_card_congr e]
  have hh := CFSGGTwoProperIndexComponentCube.order_mul_outer_cube_le_proper_index
    q hs hn (K.map e.toMonoidHom) hmap
  have hi : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
  rwa [hi] at hh

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
