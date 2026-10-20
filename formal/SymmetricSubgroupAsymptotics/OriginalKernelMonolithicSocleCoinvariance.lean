import SymmetricSubgroupAsymptotics.OriginalKernelSocleActionKernel
import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction

/-! Genuine original-normal-denominator bridge for a monolithic linear
image. Either the whole original quotient socle stays in its literal
translation kernel, or the actual linear monolith acts trivially on the
ENTIRE retained translation section. No split extension is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {p : ℕ} {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep.{0} (ZMod p) B) (E : OriginalKernelModuleChart pi A)
  (N : Subgroup G) [N.Normal]

include E in
theorem retained_monolith_coinvariance (hpi : Function.Surjective pi)
    (L : Subgroup B)
    (hmono : ∀ D : Subgroup B, D.Normal → D≠⊥ → L≤D) :
    finiteGroupSocle (G ⧸ N)≤(base pi N).ker ∨
      L≤((E.sectionRepresentation pi A N).ρ.asGroupHom.comp
        (sectionTop pi N hpi)).ker := by
  let f := base pi N
  let s := sectionTop pi N hpi
  let M := (finiteGroupSocle (G ⧸ N)).map f
  have hs : Function.Surjective s := by
    intro y
    obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) y
    exact ⟨pi g,(sectionTop_apply pi N hpi g).trans hg⟩
  by_cases hm : M=⊥
  · left
    intro x hx
    have hmx : f x∈M := ⟨x,hx,rfl⟩
    rw [hm] at hmx
    exact Subgroup.mem_bot.mp hmx
  · right
    letI : M.Normal := Subgroup.Normal.map inferInstance f (base_surjective pi N)
    let D := M.comap s
    letI : D.Normal := Subgroup.Normal.comap inferInstance s
    have hd : D≠⊥ := by
      intro h
      have he : D.map s=M := Subgroup.map_comap_eq_self_of_surjective hs M
      rw [h,Subgroup.map_bot] at he
      exact hm he.symm
    have hl : L≤D := hmono D inferInstance hd
    intro l hll
    have hlm : s l∈M := hl hll
    have hact := E.retainedSocle_map_le_actionKernel pi A N hlm
    exact hact

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
