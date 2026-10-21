import SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveTransvectionGeometry

/-! Exact membership in the original projective point-root groups is
recovered from the original centre line of a nonidentity transvection.
Projective nontriviality follows from the actual root parameter injection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootMembership
open Matrix Module LinearMap Submodule CFSGTypeAProjectivePointRoots
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem projective_transvection_ne_one {f : Dual F (n→F)} {v : n→F}
    (hfv : f v=0) (hf : f≠0) (hv : v≠0) : projection (transvectionSL hfv)≠1 := by
  intro he
  let z : Multiplicative (pointForms v) := Multiplicative.ofAdd ⟨f,hfv⟩
  have hz : pointRootHom v z=pointRootHom v 1 := by
    rw [map_one]
    exact he
  have hh := congrArg (fun a : Multiplicative (pointForms v) => a.toAdd.val)
    (pointRootHom_injective hv hz)
  exact hf hh

theorem pointRoot_mem_iff_centre (hn : 3≤Fintype.card n)
    {f : Dual F (n→F)} {v w : n→F} (hfv : f v=0) (hf : f≠0) (hv : v≠0) :
    projection (transvectionSL hfv)∈pointRoot w ↔ (F ∙ v)=(F ∙ w) := by
  constructor
  · rintro ⟨g,hg⟩
    have hg0 : g.toAdd.val≠0 := by
      intro he
      have hzero : g.toAdd=0 := Subtype.ext he
      have hgone : g=1 := congrArg Multiplicative.ofAdd hzero
      rw [hgone,map_one] at hg
      exact projective_transvection_ne_one hfv hf hv hg.symm
    have he : projection (transvectionSL hfv)=projection
        (transvectionSL (show g.toAdd.val w=0 from g.toAdd.property)) := hg.symm
    exact centre_eq_of_projective_transvection_eq hn hfv g.toAdd.property hf hg0 he
  · intro hc
    have hvspan : v∈F ∙ w := by
      rw [←hc]
      exact Submodule.mem_span_singleton_self v
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hvspan
    have hform : (a • f) w=0 := by
      have hh : f (a • w)=0 := by rw [ha];exact hfv
      simpa only [map_smul,LinearMap.smul_apply] using hh
    let g : Multiplicative (pointForms w) := Multiplicative.ofAdd ⟨a • f,hform⟩
    refine ⟨g,?_⟩
    change projection (transvectionSL hform)=projection (transvectionSL hfv)
    apply congrArg projection
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro x
    rw [transvectionSL_apply,transvectionSL_apply,←ha]
    simp only [LinearMap.smul_apply,smul_smul,smul_eq_mul,mul_comm]

end SymmetricSubgroupAsymptotics.CFSGTypeARootMembership
