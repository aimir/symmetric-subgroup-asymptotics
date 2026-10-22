import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPlaneAction
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyFaithfulness

/-! Faithfulness of the SAME original projective B automorphism action
on singular planes. Nontriviality and properness of a literal root label
are proved using its additive parameters and the checked trivial centre.
Simplicity is exactly the model property transported from classification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBIntrinsicLongRoots
variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem highestRootLine_ne_bot (h2 : (2 : K) ≠ 0) (s : ℕ) :
    highestRootLine (K:=K) h2 s≠⊥ := by
  intro hb
  have hm : highestRoot (K:=K) s 1∈highestRootLine h2 s :=
    (mem_highestRootLine_iff h2 s _).mpr ⟨1,rfl⟩
  rw [hb] at hm
  have hz : highestRoot (K:=K) s 1=1 := Subgroup.mem_bot.mp hm
  exact one_ne_zero (highestRoot_injective h2 s (hz.trans (highestRoot_zero h2 s).symm))

omit [Finite K] in
theorem highestRootLine_ne_top (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) : highestRootLine (K:=K) h2 s≠⊤ := by
  intro ht
  have hc : highestRoot (K:=K) s 1∈Subgroup.center (elementaryRootGroup K (s+3)) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hy : y∈highestRootLine h2 s := by rw [ht];trivial
    obtain ⟨a,rfl⟩ := (mem_highestRootLine_iff h2 s y).mp hy
    rw [←highestRoot_add h2 s a 1,←highestRoot_add h2 s 1 a]
    exact congrArg (highestRoot (K:=K) s) (add_comm a 1)
  rw [CFSGOrthogonalBIndexCenter.center_eq_bot K p h2 (s+2)] at hc
  have hz : highestRoot (K:=K) s 1=1 := Subgroup.mem_bot.mp hc
  exact one_ne_zero (highestRoot_injective h2 s (hz.trans (highestRoot_zero h2 s).symm))

theorem exists_singularLabel_nontrivial_proper (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) :
    ∃P : SingularPlanes (K:=K) s,singularLabel h2 s P≠⊥ ∧ singularLabel h2 s P≠⊤ := by
  let e := oddProjectiveEquiv K p h2 (s+2)
  let P := (singularPlaneEquiv (K:=K) h2 s).symm (plane s 1)
  have hl : singularLabel h2 s P=(highestRootLine h2 s).map e.toMonoidHom := by
    change projectiveLabel h2 s ((singularPlaneEquiv h2 s)
      ((singularPlaneEquiv h2 s).symm (plane s 1)))=_
    rw [(singularPlaneEquiv h2 s).apply_symm_apply,projectiveLabel_plane]
    change (conjugateRootLine h2 s 1).map e.toMonoidHom=_
    congr 1
    change (highestRootLine h2 s).map (MulAut.conj 1).toMonoidHom=highestRootLine h2 s
    have hc : (MulAut.conj (1 : elementaryRootGroup K (s+3))).toMonoidHom=MonoidHom.id _ := by
      ext x
      simp
    rw [hc]
    exact Subgroup.map_id _
  refine ⟨P,?_,?_⟩
  · intro hb
    have hm : e (highestRoot (K:=K) s 1)∈singularLabel h2 s P := by
      rw [hl]
      exact ⟨highestRoot s 1,(mem_highestRootLine_iff h2 s _).mpr ⟨1,rfl⟩,rfl⟩
    rw [hb] at hm
    have he : e (highestRoot (K:=K) s 1)=1 := Subgroup.mem_bot.mp hm
    have hz := e.injective (he.trans e.map_one.symm)
    exact one_ne_zero (highestRoot_injective h2 s (hz.trans (highestRoot_zero h2 s).symm))
  · intro ht
    have heq : (highestRootLine h2 s).map e.toMonoidHom=(⊤ : Subgroup
        (elementaryRootGroup K (s+3))).map e.toMonoidHom := by
      exact hl.symm.trans (ht.trans
        (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm)
    exact highestRootLine_ne_top p h2 s (Subgroup.map_injective (f:=e.toMonoidHom) e.injective heq)

theorem singularActionHom_injective (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) [IsSimpleGroup (elementaryProjective K (s+3))] :
    Function.Injective (singularActionHom (K:=K) p h2 s) := by
  obtain ⟨P,hne,hproper⟩ := exists_singularLabel_nontrivial_proper p h2 s
  let rho := CFSGSubgroupFamilyPermutation.permutationHom (singularLabel h2 s)
    (singularLabel_injective p h2 s) (singular_stable p h2 s)
  have hi : Function.Injective rho := CFSGSubgroupFamilyFaithfulness.permutationHom_injective
    (singularLabel h2 s) (singularLabel_injective p h2 s) (singular_stable p h2 s) P hne hproper
  have heq : singularActionHom p h2 s=rho := by
    apply MonoidHom.ext
    intro f
    apply Equiv.ext
    intro Q
    apply singularLabel_injective p h2 s
    exact (singularLabel_action p h2 s f Q).trans
      (CFSGSubgroupFamilyPermutation.label_permutation (singularLabel h2 s)
        (singularLabel_injective p h2 s) (singular_stable p h2 s) f Q).symm
  rw [heq]
  exact hi

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
