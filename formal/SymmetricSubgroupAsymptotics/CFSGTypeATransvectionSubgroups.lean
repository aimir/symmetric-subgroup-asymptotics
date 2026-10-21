import SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveRootFamilies
import SymmetricSubgroupAsymptotics.CFSGTypeAHyperplaneMembership
import Mathlib.Tactic.Choose

/-! A nontrivial subgroup consisting entirely of original projective
transvections is contained in one original point-root or hyperplane-root
group. Nonidentity elements keep explicit original representative forms
and vectors; closure gives the actual rank-one product condition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeATransvectionSubgroups
open Matrix Module LinearMap Submodule CFSGTypeAProjectivePointRoots CFSGTypeAHyperplaneRoots
open CFSGTypeARootMembership CFSGTypeAProjectiveRootFamilies CFSGTypeAProjectiveTransvectionRecognition
variable {F : Type*} [Field F] {n : ℕ}

theorem subgroup_le_point_or_hyperplane (hn : 3≤n)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F)) (hH : H≠⊥)
    (hAll : ∀x,x∈H→IsProjectiveTransvection x) :
    (∃v : Fin n→F,v≠0 ∧ H≤pointRoot v) ∨
      (∃f : Dual F (Fin n→F),f≠0 ∧ H≤hyperplaneRoot f) := by
  classical
  let I := {x : H // x≠1}
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  let i0 : I := ⟨z,hz⟩
  have hdata : ∀i : I,∃f : Dual F (Fin n→F),∃v : Fin n→F,∃hfv : f v=0,
      ((i.val : H) : Matrix.ProjectiveSpecialLinearGroup (Fin n) F)=projection (transvectionSL hfv) := by
    intro i
    exact hAll _ i.val.property
  choose f v hfv he using hdata
  have hnon : ∀i : I,((i.val : H) : Matrix.ProjectiveSpecialLinearGroup (Fin n) F)≠1 := by
    intro i hi
    exact i.property (Subtype.ext hi)
  have hf : ∀i : I,f i≠0 := by
    intro i hi
    have hzero : transvectionSL (hfv i)=1 := by
      apply Matrix.SpecialLinearGroup.toLin'_injective
      rw [map_one]
      apply LinearEquiv.ext
      intro x
      change (transvectionSL (hfv i)).toLin' x=x
      simp only [transvectionSL_apply,hi,LinearMap.zero_apply,zero_smul,add_zero]
    apply hnon i
    rw [he i,hzero,map_one]
  have hv : ∀i : I,v i≠0 := by
    intro i hi
    have hzero : transvectionSL (hfv i)=1 := by
      apply Matrix.SpecialLinearGroup.toLin'_injective
      rw [map_one]
      apply LinearEquiv.ext
      intro x
      change (transvectionSL (hfv i)).toLin' x=x
      simp only [transvectionSL_apply,hi,smul_zero,add_zero]
    apply hnon i
    rw [he i,hzero,map_one]
  have hprod : ∀i j : I,IsProjectiveTransvection
      (projection (transvectionSL (hfv i))*projection (transvectionSL (hfv j))) := by
    intro i j
    have hh := hAll _ (H.mul_mem i.val.property j.val.property)
    simpa only [he i,he j] using hh
  rcases common_centre_or_axis_of_projective_products hn f v hfv hf hv hprod with hc|ha
  · left
    refine ⟨v i0,hv i0,?_⟩
    intro x hx
    by_cases hx1 : x=1
    · rw [hx1]
      exact (pointRoot (v i0)).one_mem
    · let i : I := ⟨⟨x,hx⟩,by intro h;exact hx1 (congrArg Subtype.val h)⟩
      have hm := (pointRoot_mem_iff_centre
        (by simpa only [Fintype.card_fin] using hn) (hfv i) (hf i) (hv i)).mpr (hc i i0)
      rw [←he i] at hm
      exact hm
  · right
    refine ⟨f i0,hf i0,?_⟩
    intro x hx
    by_cases hx1 : x=1
    · rw [hx1]
      exact (hyperplaneRoot (f i0)).one_mem
    · let i : I := ⟨⟨x,hx⟩,by intro h;exact hx1 (congrArg Subtype.val h)⟩
      have hm := (hyperplaneRoot_mem_iff_axis
        (by simpa only [Fintype.card_fin] using hn) (hfv i) (hf i) (hf i0) (hv i)).mpr (ha i i0)
      rw [←he i] at hm
      exact hm

end SymmetricSubgroupAsymptotics.CFSGTypeATransvectionSubgroups
