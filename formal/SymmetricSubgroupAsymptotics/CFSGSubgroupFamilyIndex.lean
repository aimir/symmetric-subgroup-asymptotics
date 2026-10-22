import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyStabilizer
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Perm

/-! Bound the index of the pointwise family stabilizer by the actual
finite family of permitted permutations. Chosen permutations suffice;
there is no assumed permutation-action homomorphism. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyIndex
open CFSGSubgroupFamilyStabilizer
variable {G I : Type*} [Group G] [Fintype I]

theorem family_index_le_permutations (B : Subgroup (MulAut G)) (S : I → Subgroup G)
    (P : Equiv.Perm I → Prop)
    (hperm : ∀ f : B, ∃ σ : Equiv.Perm I, P σ ∧
      ∀ j, (S j).map f.val.toMonoidHom = S (σ j)) :
    ((familyStabilizer S).subgroupOf B).index ≤ Nat.card {σ : Equiv.Perm I // P σ} := by
  classical
  let T := (familyStabilizer S).subgroupOf B
  choose σ hσ ha using hperm
  let enc : B ⧸ T → {τ : Equiv.Perm I // P τ} := fun q => ⟨σ q.out, hσ q.out⟩
  have hinj : Function.Injective enc := by
    intro x y he
    have hxy : σ x.out = σ y.out := congrArg Subtype.val he
    have hT : y.out⁻¹ * x.out ∈ T := by
      change ∀ j, (S j).map (y.out.val.symm * x.out.val).toMonoidHom = S j
      intro j
      have hc : (y.out.val.symm * x.out.val).toMonoidHom =
          y.out.val.symm.toMonoidHom.comp x.out.val.toMonoidHom := rfl
      rw [hc, ← Subgroup.map_map, ha x.out j, hxy, ← ha y.out j, Subgroup.map_map]
      have hi : y.out.val.symm.toMonoidHom.comp y.out.val.toMonoidHom = MonoidHom.id G := by
        ext z
        exact y.out.val.symm_apply_apply z
      rw [hi, Subgroup.map_id]
    have heq : (x.out : B ⧸ T) = y.out := QuotientGroup.eq.mpr (by
      simpa only [mul_inv_rev, inv_inv] using T.inv_mem hT)
    exact x.out_eq'.symm.trans (heq.trans y.out_eq')
  rw [Subgroup.index_eq_card]
  exact Nat.card_le_card_of_injective enc hinj

end SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyIndex
