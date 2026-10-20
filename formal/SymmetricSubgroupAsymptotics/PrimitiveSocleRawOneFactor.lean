import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import Mathlib.Order.Preorder.Finite

/-! A one-factor FULL socle is contained in every nontrivial ambient
normal subgroup. This deduction is deliberately absent from the raw input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

private theorem minimalNormal_exists {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    ∃ M : Subgroup G, IsMinimalNormalSubgroup M ∧ M ≤ N := by
  let good : Subgroup G → Prop := fun M => M.Normal ∧ M ≠ ⊥
  obtain ⟨M,hMN,hminimal⟩ :=
    Finite.exists_le_minimal (p := good) (a := N) ⟨inferInstance,hN⟩
  refine ⟨M,⟨hminimal.1.1,hminimal.1.2,?_⟩,hMN⟩
  intro K hKn hKne hKM
  exact hminimal.eq_of_le ⟨hKn,hKne⟩ hKM

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

def NonaffineData.oneFactorEquiv (D : NonaffineData G X)
    (hk : D.factorCount = 1) : finiteGroupSocle G ≃* D.Simple :=
  D.socleEquiv.trans
    { toFun := fun f => f ⟨0,D.factorCount_pos⟩
      invFun := fun t _ => t
      left_inv := by
        intro f
        funext i
        have hi : i = ⟨0,D.factorCount_pos⟩ := by
          apply Fin.ext
          have := i.isLt
          omega
        rw [hi]
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }

theorem NonaffineData.oneFactor_socle_nontrivial (D : NonaffineData G X)
    (hk : D.factorCount = 1) : finiteGroupSocle G ≠ ⊥ := by
  letI : IsSimpleGroup (finiteGroupSocle G) := (D.oneFactorEquiv hk).isSimpleGroup
  exact (Subgroup.isSimpleGroup_iff.mp inferInstance).1

theorem NonaffineData.oneFactor_socle_le (D : NonaffineData G X)
    (hk : D.factorCount = 1) (N : Subgroup G) (hNn : N.Normal)
    (hN : N ≠ ⊥) : finiteGroupSocle G ≤ N := by
  letI : N.Normal := hNn
  obtain ⟨M,hM,hMN⟩ := minimalNormal_exists N hN
  letI : M.Normal := hM.1
  have hME : M ≤ finiteGroupSocle G := by
    intro m hm
    exact Subgroup.subset_normalClosure ⟨M,hM,hm⟩
  letI : IsSimpleGroup (finiteGroupSocle G) := (D.oneFactorEquiv hk).isSimpleGroup
  have hcases := (Subgroup.isSimpleGroup_iff.mp
    (inferInstance : IsSimpleGroup (finiteGroupSocle G))).2 M hME
      (show (M.subgroupOf (finiteGroupSocle G)).Normal from inferInstance)
  rcases hcases with hbot | htop
  · exact False.elim (hM.2.1 hbot)
  · exact htop ▸ hMN

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
