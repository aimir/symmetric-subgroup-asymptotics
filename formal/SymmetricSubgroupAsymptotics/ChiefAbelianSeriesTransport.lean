import SymmetricSubgroupAsymptotics.ChiefSeriesTransport
import SymmetricSubgroupAsymptotics.ChiefAbelianCompositionLength

/-! Abelian and nonabelian chief charges are invariant under literal group
equivalence, factor by factor. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G R : Type} [Group G] [Group R] [Finite G] [Finite R]

theorem actualChiefSeriesComap_abelianLength
    (e : R ≃* G) (s : ActualChiefSeries G) :
    actualChiefSeriesAbelianLength (actualChiefSeriesComap e s) =
      actualChiefSeriesAbelianLength s := by
  apply Finset.sum_congr rfl
  intro i _
  exact chiefAbelianLength_congr (normalChainQuotientComapEquiv e
    (s.subgroup i.castSucc) (s.subgroup i.succ))

theorem actualChiefSeriesComap_nonabelianCount
    (e : R ≃* G) (s : ActualChiefSeries G) :
    actualChiefSeriesNonabelianCount (actualChiefSeriesComap e s) =
      actualChiefSeriesNonabelianCount s := by
  apply Finset.sum_congr rfl
  intro i _
  exact chiefNonabelianIndicator_congr (normalChainQuotientComapEquiv e
    (s.subgroup i.castSucc) (s.subgroup i.succ))

end SymmetricSubgroupAsymptotics

end
