import Mathlib.GroupTheory.Nilpotent

/-! A finite p-subgroup is Sylow if its normalizer contains no larger
p-subgroup. This uses the normalizer condition inside the actual original
p-overgroup, with no group-order or subgroup-index formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality

theorem maximal_of_normalizer_pGroups {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (U : Subgroup G)
    (hN : ∀ P : Subgroup G,IsPGroup p P →
      P≤Subgroup.normalizer (U : Set G) → P≤U)
    (Q : Subgroup G) (hQ : IsPGroup p Q) (hUQ : U≤Q) : Q=U := by
  let R := U.subgroupOf Q
  let N := Subgroup.normalizer (R : Set Q)
  have hRmap : R.map Q.subtype=U := by
    rw [Subgroup.subgroupOf_map_subtype,inf_of_le_left hUQ]
  have hPN : IsPGroup p (N.map Q.subtype) := (hQ.to_subgroup N).map Q.subtype
  have hNmap : N.map Q.subtype≤U := by
    apply hN _ hPN
    have hm := R.le_normalizer_map Q.subtype
    rw [hRmap] at hm
    exact hm
  have hNR : N≤R := by
    intro x hx
    exact hNmap ⟨x,hx,rfl⟩
  letI : Group.IsNilpotent Q := hQ.isNilpotent
  have hRtop : R=⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent R (le_antisymm hNR R.le_normalizer)
  apply le_antisymm _ hUQ
  intro x hx
  have hm : (⟨x,hx⟩ : Q)∈R := by rw [hRtop];exact Subgroup.mem_top _
  exact hm

def sylowOfNormalizer {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (U : Subgroup G) (hU : IsPGroup p U)
    (hN : ∀ P : Subgroup G,IsPGroup p P →
      P≤Subgroup.normalizer (U : Set G) → P≤U) : Sylow p G where
  toSubgroup := U
  isPGroup' := hU
  is_maximal' := fun {Q} hQ hUQ => maximal_of_normalizer_pGroups U hN Q hQ hUQ

end SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality
