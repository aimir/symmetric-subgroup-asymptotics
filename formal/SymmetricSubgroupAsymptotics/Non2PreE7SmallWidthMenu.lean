import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveRecoveredNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure
import SymmetricSubgroupAsymptotics.Non2PreE7SmallWidthFourClassification
import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailDecay

/-!
# The finite pre-E7 menu at width four

A transitive subgroup of `S₄` has order divisible by four.  If it is proper,
its order is therefore `4`, `8`, or `12`; the first two possibilities are
2-groups.  Hence a retained non-2 action is literally the natural `A₄`
action or the full natural `S₄` action.

The two alternatives are sent to their already checked numerical sources:
the correlated natural-`A₄` row and the ordinary `S₄` comparator row.  This
file deliberately states the result at width four.  Width three belongs to
the complete low natural packet, whose estimate is global in the number of
actual `C₃`/`A₄` orbits and is not a pointwise affine-action row.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The exact numerical source attached to a retained width-four action. -/
noncomputable def preE7WidthFourRankTailOwnerSource
    (U : PreE7NonPairActionClass 4) :
    PreE7RankTailOwnerSourceData 4 U := by
  by_cases hA4 : preE7NonPairAction 4 U = alternatingGroup (Fin 4)
  · exact .ordinary .saprim (.package
      (PreE7NaturalA4Source.numericalPackage
        ({ degree := rfl, alternating := hA4 } :
          PreE7NaturalA4Source 4 U)))
  · have hS4 :=
      (preE7NonPairAction_degreeFour_eq_alternating_or_top U).resolve_left hA4
    exact .ordinary .s4 (.small
      (preE7_s4_numericalData 4 U
        ({ degree := rfl, full := hS4 } : PreE7S4Source 4 U)))

/-- Width four is completely discharged in the source-or-Yoneda-top
interface used by the primitive catalogue assembly. -/
noncomputable def preE7WidthFourSourceOrYonedaTop
    (U : PreE7NonPairActionClass 4) :
    PreE7RankTailSourceOrYonedaTopData 4 U :=
  .inl (preE7WidthFourRankTailOwnerSource U)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
