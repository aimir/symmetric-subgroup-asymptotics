import SymmetricSubgroupAsymptotics.OrderFourQuotientLifting
import SymmetricSubgroupAsymptotics.MinimalNormalIsotypicRelativeOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleAffineAlternative
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScott
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOrderFour

/-! One actual elementary Sylow excludes order four in the original
source and each actual simple factor of its retained socle chart.
The literal Mathieu22 order-four element is therefore incompatible with
that factor. No point-degree, known model order, or model recognition
assumption is used; the SAME internal factor embeds into the original G. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleElementarySylowOrderFourExclusion
open PrimitiveSocleRawStructure

theorem no_order_four_of_elementary_sylow {G : Type} [Group G] [Finite G]
    (P : Sylow 2 G) (hel : ∀ g : P, g^2 = 1) : ¬∃ g : G, orderOf g = 4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply OrderFourQuotientLifting.no_order_four_of_elementary_sylows
  intro Q x
  let e : Q ≃* P := Q.equiv P
  apply e.injective
  rw [map_pow,map_one]
  exact hel (e x)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem simple_no_order_four (P : Sylow 2 G) (hel : ∀ g : P, g^2 = 1) :
    ¬∃ g : D.Simple, orderOf g = 4 := by
  let i : Fin D.factorCount := ⟨0,D.factorCount_pos⟩
  let f : D.Simple →* G := MinimalNormalIsotypicRelativeOrdinaryGenerators.axisHom
    (finiteGroupSocle G) D.socleEquiv i
  have hf : Function.Injective f := Subtype.coe_injective.comp
    (MinimalNormalIsotypicRelativeOrdinaryGenerators.axisMap_injective
      (finiteGroupSocle G) D.socleEquiv i)
  rintro ⟨g,hg⟩
  exact no_order_four_of_elementary_sylow P hel
    ⟨f g,(orderOf_injective f hf g).trans hg⟩

theorem not_mathieu_twenty_two (P : Sylow 2 G) (hel : ∀ g : P, g^2 = 1)
    (e : D.Simple ≃* CFSG.Models.Mathieu22) : False := by
  obtain ⟨g,hg⟩ := CFSGMathieuTwentyTwoOrderFour.exists_order_four
  exact simple_no_order_four D P hel ⟨e.symm g,(e.symm.orderOf_eq g).trans hg⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleElementarySylowOrderFourExclusion
