import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-! An abelian normal translation image acts trivially on the whole socle.
The quotient statement keeps the original normal denominator explicitly. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G]

/-- Minimal normal subgroups centralize an abelian normal subgroup. -/
theorem minimalNormal_le_centralizer_of_abelian_normal
    (T M : Subgroup G) [T.Normal] [IsMulCommutative T]
    (hM : IsMinimalNormalSubgroup M) :
    M ≤ Subgroup.centralizer (T : Set G) := by
  letI : M.Normal := hM.1
  have hbot : ⁅T, M⁆ = ⊥ := by
    rcases minimalNormal_commutator_full_or_trivial T M hM with hfull | hzero
    · have hMT : M ≤ T := by
        rw [← hfull]
        exact Subgroup.commutator_le_left T M
      have hTT : ⁅T, T⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
      exact le_antisymm
        ((Subgroup.commutator_mono le_rfl hMT).trans_eq hTT) bot_le
    · exact hzero
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
  rw [Subgroup.commutator_comm]
  exact hbot

/-- The action on the full original socle factors through any quotient by
an abelian normal subgroup. This includes all prime-primary socle parts. -/
theorem finiteGroupSocle_le_centralizer_of_abelian_normal
    (T : Subgroup G) [T.Normal] [IsMulCommutative T] :
    finiteGroupSocle G ≤ Subgroup.centralizer (T : Set G) := by
  unfold finiteGroupSocle
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨M, hM, hx⟩
  exact minimalNormal_le_centralizer_of_abelian_normal T M hM hx

/-- Literal retained-image form: no replacement of the denominator or
isomorphism-class representative is made. -/
theorem retainedTranslation_socle_centralizes
    (T N : Subgroup G) [T.Normal] [N.Normal]
    [IsMulCommutative (T.map (QuotientGroup.mk' N))] :
    finiteGroupSocle (G ⧸ N) ≤
      Subgroup.centralizer ((T.map (QuotientGroup.mk' N)) : Set (G ⧸ N)) := by
  letI : (T.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  exact finiteGroupSocle_le_centralizer_of_abelian_normal _

end SymmetricSubgroupAsymptotics
