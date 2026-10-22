import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborAdjacency

/-! The three local coordinate-axis families have literal global
geometric meanings: a singular three-space top, or an incident-point
star inside one of the two genuine maximal-extension components.
This identifies sets of ORIGINAL planes, not just coordinate labels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

theorem neighbor_threeSpace_eq_iff_le (S : Neighbors K) (W : ThreeExtensions K) :
    neighborThreeSpace K S = W ↔ S.val ≤ W.val := by
  constructor
  · intro he
    exact (neighbor_le_threeSpace K S).trans (congrArg Subtype.val he).le
  · intro hS
    apply Subtype.ext
    exact Submodule.eq_of_le_of_finrank_le (sup_le W.property.2.2 hS)
      (by rw [W.property.1, (neighborThreeSpace K S).property.1])

theorem neighbor_point_eq_iff_le (S : Neighbors K) (U : RootPoints K) :
    neighborPoint K S = U ↔ U.val ≤ S.val := by
  constructor
  · intro he
    exact (congrArg Subtype.val he).ge.trans (neighbor_point_le K S)
  · intro hS
    apply Subtype.ext
    apply Eq.symm
    exact Submodule.eq_of_le_of_finrank_le (le_inf U.property.2 hS)
      (by rw [(neighborPoint K S).property.1, U.property.1])

theorem neighbor_parameters_eq_iff_top (S : Neighbors K) (p q : RulingParameters K) :
    neighborOppositeParameters K S = (p, q) ↔
      S.val ≤ (threeExtensionRulingEquiv K (p, q)).val := by
  rw [← neighbor_threeSpace_eq_iff_le]
  constructor
  · intro he
    exact (neighborThreeSpace_eq_parameters K S).trans (congrArg (threeExtensionRulingEquiv K) he)
  · intro he
    have hh := congrArg (fun W => (threeExtensionRulingEquiv K).symm W) he
    exact hh.trans ((threeExtensionRulingEquiv K).symm_apply_apply (p, q))

theorem neighbor_point_column_iff_star (S : Neighbors K) (U : RootPoints K)
    (p : RulingParameters K) :
    (neighborPoint K S = U ∧ (neighborOppositeParameters K S).1 = p) ↔
      (U.val ≤ S.val ∧ S.val ≤ (columnMaximalExtension K p).val) := by
  rw [neighbor_point_eq_iff_le]
  have hcol : (neighborOppositeParameters K S).1 = p ↔
      S.val ≤ (columnMaximalExtension K p).val := by
    have hh := threeExtension_le_column_iff K
      (neighborOppositeParameters K S).1 (neighborOppositeParameters K S).2 p
    rw [← neighborThreeSpace_eq_parameters K S] at hh
    constructor
    · intro hp
      exact (neighbor_le_threeSpace K S).trans (hh.mpr hp)
    · intro hS
      exact hh.mp (sup_le (columnMaximalExtension K p).property.2.2 hS)
  exact and_congr_right (fun _ => hcol)

theorem neighbor_point_row_iff_star (S : Neighbors K) (U : RootPoints K)
    (q : RulingParameters K) :
    (neighborPoint K S = U ∧ (neighborOppositeParameters K S).2 = q) ↔
      (U.val ≤ S.val ∧ S.val ≤ (rowMaximalExtension K q).val) := by
  rw [neighbor_point_eq_iff_le]
  have hrow : (neighborOppositeParameters K S).2 = q ↔
      S.val ≤ (rowMaximalExtension K q).val := by
    have hh := threeExtension_le_row_iff K
      (neighborOppositeParameters K S).1 (neighborOppositeParameters K S).2 q
    rw [← neighborThreeSpace_eq_parameters K S] at hh
    constructor
    · intro hq
      exact (neighbor_le_threeSpace K S).trans (hh.mpr hq)
    · intro hS
      exact hh.mp (sup_le (rowMaximalExtension K q).property.2.2 hS)
  exact and_congr_right (fun _ => hrow)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
