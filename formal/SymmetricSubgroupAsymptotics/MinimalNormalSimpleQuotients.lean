import SymmetricSubgroupAsymptotics.ChiefConjugateIntersections
import SymmetricSubgroupAsymptotics.MaximalNormalQuotient
import Mathlib.GroupTheory.IsPerfect

/-! A finite nonabelian minimal normal subgroup has literal jointly faithful
surjections onto simple perfect groups. We use the ambient conjugates of one
maximal normal kernel. This avoids assuming a direct-product classification
and retains the original ambient conjugation action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics


section Minimal
variable {A : Type} [Group A] (N : Subgroup A) [N.Normal]
variable (hmin : ∀ K : Subgroup A, K.Normal → K≤N → K=⊥ ∨ K=N)
include hmin

theorem nonabelian_minimal_normal_perfect (hnc : ¬IsMulCommutative N) :
    Group.IsPerfect N := by
  let D := (commutator N).map N.subtype
  have hn : D.Normal := inferInstance
  rcases hmin D hn (Subgroup.map_subtype_le _) with hd|hd
  · have he : commutator N=⊥ := by
      apply Subgroup.map_injective N.subtype_injective
      simpa only [Subgroup.map_bot] using hd
    exact (hnc ((commutator_eq_bot_iff N).mp he)).elim
  · constructor
    apply Subgroup.map_injective N.subtype_injective
    simpa only [D,←MonoidHom.range_eq_map,Subgroup.range_subtype] using hd

theorem minimal_normal_quotient_conjugates_separate (M : Subgroup N) [M.Normal]
    (hM : M≠⊤) :
    ∀ n:N, (∀a:A,QuotientGroup.mk' M (MulAut.conjNormal a n)=1) → n=1 := by
  have hc : localChiefIntersection N (MonoidHom.id N) M=⊥ := by
    rcases hmin _ (localChiefIntersection_normal N (MonoidHom.id N) M)
      (localChiefIntersection_le N (MonoidHom.id N) M) with h|h
    · exact h
    · exfalso
      apply hM
      apply top_unique
      intro n _
      have hn : (n:A)∈localChiefIntersection N (MonoidHom.id N) M := by
        rw [h]
        exact n.2
      have he := (mem_localChiefIntersection N (MonoidHom.id N) M n).mp hn 1
      simpa using he
  intro n hn
  have he : (n:A)∈localChiefIntersection N (MonoidHom.id N) M := by
    apply (mem_localChiefIntersection N (MonoidHom.id N) M n).mpr
    intro a
    exact (QuotientGroup.eq_one_iff _).mp (hn a)
  rw [hc] at he
  exact Subtype.ext he

theorem minimal_normal_quotient_conjugates_injective (M : Subgroup N) [M.Normal]
    (hM : M≠⊤) :
    Function.Injective (fun n:N => fun a:A =>
      QuotientGroup.mk' M (MulAut.conjNormal a n)) := by
  intro n m he
  apply mul_inv_eq_one.mp
  apply minimal_normal_quotient_conjugates_separate N hmin M hM
  intro a
  simp only [map_mul,map_inv]
  exact mul_inv_eq_one.mpr (congrFun he a)

/-- Actual finite simple quotient data for a nonabelian minimal normal group.
Every coordinate is an original conjugation followed by one literal quotient;
no abstractly isomorphic source replaces the original subgroup. -/
theorem nonabelian_minimal_normal_simple_coordinates [Finite A]
    (hnc : ¬IsMulCommutative N) :
    ∃ (M : Subgroup N) (_hM : M.Normal),
      IsSimpleGroup (N⧸M) ∧ Group.IsPerfect (N⧸M) ∧
      (∀a:A,Function.Surjective
        ((QuotientGroup.mk' M).comp (MulAut.conjNormal a).toMonoidHom)) ∧
      Function.Injective (fun n:N => fun a:A =>
        QuotientGroup.mk' M (MulAut.conjNormal a n)) := by
  letI : Group.IsPerfect N := nonabelian_minimal_normal_perfect N hmin hnc
  haveI : Nontrivial N := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    letI := hs
    exact hnc ⟨⟨fun x y=>Subsingleton.elim _ _⟩⟩)
  obtain ⟨M,hm,hM,hmax⟩ := finite_exists_maximal_normal N
  letI := hm
  exact ⟨M,hm,maximal_normal_quotient_simple N M hM hmax,inferInstance,
    fun a=>(QuotientGroup.mk'_surjective M).comp (MulAut.conjNormal a).surjective,
    minimal_normal_quotient_conjugates_injective N hmin M hM⟩

end Minimal
end SymmetricSubgroupAsymptotics
