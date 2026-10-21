import SymmetricSubgroupAsymptotics.CFSGTypeARootLabels

/-! The original point and hyperplane root groups are disjoint labelled
families. Their nontrivial intersections recover precisely the original
point-hyperplane incidence relation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootIncidence
open Matrix Module LinearMap Submodule CFSGTypeAProjectivePointRoots CFSGTypeAHyperplaneRoots
open CFSGTypeARootMembership CFSGTypeARootLabels
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem pointRoot_inf_hyperplaneRoot_ne_bot (hn : 3≤Fintype.card n)
    {v : n→F} {f : Dual F (n→F)} (hv : v≠0) (hf : f≠0) :
    pointRoot v ⊓ hyperplaneRoot f≠⊥ ↔ f v=0 := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
    have hxval : (x : PSL (F:=F) (n:=n))≠1 := by
      intro he
      exact hx (Subtype.ext he)
    obtain ⟨g,hgx⟩ := x.property.1
    have hg : g.toAdd.val≠0 := by
      intro he
      have hz : g=1 := congrArg Multiplicative.ofAdd (Subtype.ext he)
      rw [hz,map_one] at hgx
      exact hxval hgx.symm
    have hmem : projection (transvectionSL g.toAdd.property)∈hyperplaneRoot f := by
      change pointRootHom v g∈hyperplaneRoot f
      rw [hgx]
      exact x.property.2
    have he := (hyperplaneRoot_mem_iff_axis hn g.toAdd.property hg hf hv).mp hmem
    exact he.le (show v∈LinearMap.ker g.toAdd.val from g.toAdd.property)
  · intro hfv
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    refine ⟨⟨projection (transvectionSL hfv),?_⟩,?_⟩
    · exact ⟨⟨Multiplicative.ofAdd ⟨f,hfv⟩,rfl⟩,
        ⟨Multiplicative.ofAdd ⟨v,hfv⟩,rfl⟩⟩
    · intro he
      exact projective_transvection_ne_one hfv hf hv (congrArg Subtype.val he)

theorem pointRoot_ne_hyperplaneRoot (hn : 3≤Fintype.card n)
    {v : n→F} {f : Dual F (n→F)} (hv : v≠0) (hf : f≠0) :
    pointRoot v≠hyperplaneRoot f := by
  intro he
  have hle : pointForms v≤F ∙ f := by
    intro g hg
    by_cases hg0 : g=0
    · rw [hg0]
      exact Submodule.zero_mem _
    · have hmem : projection (transvectionSL (show g v=0 from hg))∈hyperplaneRoot f := by
        rw [←he]
        exact ⟨Multiplicative.ofAdd ⟨g,hg⟩,rfl⟩
      have hker := (hyperplaneRoot_mem_iff_axis hn hg hg0 hf hv).mp hmem
      obtain ⟨a,ha⟩ := exists_unit_smul_of_ker_eq hg0 hf hker
      exact Submodule.mem_span_singleton.mpr ⟨(a : F),ha.symm⟩
  have hd := Submodule.finrank_mono hle
  rw [finrank_span_singleton hf] at hd
  have hh := pointForms_finrank_add_one hv
  omega

abbrev Vertex := (ℙ F (n→F)) ⊕ (ℙ F (Dual F (n→F)))

def rootLabel : Vertex (F:=F) (n:=n)→Subgroup (PSL (F:=F) (n:=n))
  | Sum.inl p => pointLabel p
  | Sum.inr f => hyperplaneLabel f

theorem rootLabel_injective (hn : 3≤Fintype.card n) :
    Function.Injective (rootLabel (F:=F) (n:=n)) := by
  intro x y he
  cases x with
  | inl p =>
    cases y with
    | inl q => exact congrArg Sum.inl (pointLabel_injective hn he)
    | inr f => exact False.elim (pointRoot_ne_hyperplaneRoot hn p.rep_nonzero f.rep_nonzero he)
  | inr f =>
    cases y with
    | inl p => exact False.elim (pointRoot_ne_hyperplaneRoot hn p.rep_nonzero f.rep_nonzero he.symm)
    | inr g => exact congrArg Sum.inr (hyperplaneLabel_injective hn he)

theorem labels_inf_ne_bot_iff (hn : 3≤Fintype.card n)
    (p : ℙ F (n→F)) (f : ℙ F (Dual F (n→F))) :
    pointLabel p ⊓ hyperplaneLabel f≠⊥ ↔ f.rep p.rep=0 :=
  pointRoot_inf_hyperplaneRoot_ne_bot hn p.rep_nonzero f.rep_nonzero

theorem pointLabel_mk (hn : 3≤Fintype.card n) (v : n→F) (hv : v≠0) :
    pointLabel (Projectivization.mk F v hv)=pointRoot v := by
  apply (pointRoot_eq_iff_centre hn (Projectivization.rep_nonzero _) hv).mpr
  rw [←Projectivization.submodule_eq,Projectivization.submodule_mk]

theorem hyperplaneLabel_mk (hn : 3≤Fintype.card n) (f : Dual F (n→F)) (hf : f≠0) :
    hyperplaneLabel (Projectivization.mk F f hf)=hyperplaneRoot f := by
  apply (hyperplaneRoot_eq_iff_axis hn (Projectivization.rep_nonzero _) hf).mpr
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F f hf
  rw [←ha]
  ext x
  change (a : F)*f x=0 ↔ f x=0
  simp only [mul_eq_zero,a.ne_zero,false_or]

end SymmetricSubgroupAsymptotics.CFSGTypeARootIncidence
