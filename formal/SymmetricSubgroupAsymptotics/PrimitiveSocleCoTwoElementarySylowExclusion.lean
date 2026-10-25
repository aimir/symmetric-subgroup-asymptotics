import SymmetricSubgroupAsymptotics.CFSGCoTwoElementarySylowSolvability
import SymmetricSubgroupAsymptotics.PrimitiveSocleElementarySylowOrderFourExclusion

/-! The actual Co2 factor is incompatible with one actual elementary
Sylow two-subgroup of the original source. The SAME supported socle axis
excludes order four, the literal presentation is then solvable, and actual
simple noncommutativity contradicts solvability. No model order or
capacity premise occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleCoTwoElementarySylowExclusion
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem not_co_two (P : Sylow 2 G) (hel : ∀ g : P, g^2 = 1)
    (e : D.Simple ≃* CFSG.Models.Presentations.Co2.Model) : False := by
  have hno : ¬∃ g : CFSG.Models.Presentations.Co2.Model, orderOf g = 4 := by
    rintro ⟨g,hg⟩
    exact PrimitiveSocleElementarySylowOrderFourExclusion.simple_no_order_four D P hel
      ⟨e.symm g,(e.symm.orderOf_eq g).trans hg⟩
  letI : IsSolvable CFSG.Models.Presentations.Co2.Model :=
    CFSGCoTwoElementarySylowSolvability.isSolvable_of_no_order_four hno
  letI : IsSimpleGroup CFSG.Models.Presentations.Co2.Model := e.symm.isSimpleGroup
  have hcomm : ∀ a b : CFSG.Models.Presentations.Co2.Model, a*b = b*a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  apply D.noncommutative
  apply isMulCommutative_iff.mpr
  intro a b
  apply e.injective
  rw [map_mul,map_mul,hcomm]

end SymmetricSubgroupAsymptotics.PrimitiveSocleCoTwoElementarySylowExclusion
