import SymmetricSubgroupAsymptotics.CFSGTypeARootLabels
import SymmetricSubgroupAsymptotics.CFSGIncidenceOrientation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Original projective incidence recovers joins of point lines by dual
separation. In dimension at least three its bipartite graph is connected. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveIncidence
open Module LinearMap Submodule
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

abbrev Points := ℙ F (n→F)
abbrev Hyperplanes := ℙ F (Dual F (n→F))

def Incident (p : Points (F:=F) (n:=n)) (h : Hyperplanes (F:=F) (n:=n)) : Prop :=
  h.rep p.rep=0

omit [Fintype n] [DecidableEq n] in
theorem incident_mk_form (p : Points (F:=F) (n:=n)) (f : Dual F (n→F)) (hf : f≠0) :
    Incident p (Projectivization.mk F f hf) ↔ f p.rep=0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F f hf
  unfold Incident
  rw [←ha]
  change (a : F)*f p.rep=0 ↔ f p.rep=0
  simp only [mul_eq_zero,a.ne_zero,false_or]

omit [Fintype n] [DecidableEq n] in
theorem incident_mk_vector (h : Hyperplanes (F:=F) (n:=n)) (v : n→F) (hv : v≠0) :
    Incident (Projectivization.mk F v hv) h ↔ h.rep v=0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  unfold Incident
  rw [←ha]
  change h.rep ((a : F) • v)=0 ↔ h.rep v=0
  rw [map_smul]
  change (a : F)*h.rep v=0 ↔ h.rep v=0
  simp only [mul_eq_zero,a.ne_zero,false_or]

theorem common_hyperplane (hn : 3≤Fintype.card n)
    (p q : Points (F:=F) (n:=n)) : ∃h,Incident p h ∧ Incident q h := by
  let W := p.submodule ⊔ q.submodule
  have hdim : Module.finrank F W≤2 := by
    have hh := Submodule.finrank_add_le_finrank_add_finrank p.submodule q.submodule
    rw [Projectivization.submodule_eq,Projectivization.submodule_eq,
      finrank_span_singleton p.rep_nonzero,finrank_span_singleton q.rep_nonzero] at hh
    change Module.finrank F ↥(p.submodule ⊔ q.submodule)≤2
    rw [Projectivization.submodule_eq p,Projectivization.submodule_eq q]
    exact hh
  have hd : 0<Module.finrank F W.dualAnnihilator := by
    have hh := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    rw [Module.finrank_fintype_fun_eq_card] at hh
    omega
  letI : Nontrivial W.dualAnnihilator := Module.nontrivial_of_finrank_pos hd
  obtain ⟨f,hf⟩ := exists_ne (0 : W.dualAnnihilator)
  have hf0 : f.val≠0 := fun he => hf (Subtype.ext he)
  refine ⟨Projectivization.mk F f.val hf0,?_,?_⟩
  · apply (incident_mk_form p f.val hf0).mpr
    exact (Submodule.mem_dualAnnihilator f.val).mp f.property p.rep
      ((show p.submodule≤W from le_sup_left) (by rw [Projectivization.submodule_eq];exact mem_span_singleton_self _))
  · apply (incident_mk_form q f.val hf0).mpr
    exact (Submodule.mem_dualAnnihilator f.val).mp f.property q.rep
      ((show q.submodule≤W from le_sup_right) (by rw [Projectivization.submodule_eq];exact mem_span_singleton_self _))

theorem hyperplane_has_point (hn : 2≤Fintype.card n)
    (h : Hyperplanes (F:=F) (n:=n)) : ∃p,Incident p h := by
  obtain ⟨v,hv,hfv⟩ := CFSGTypeARootLabels.exists_nonzero_kernel_vector hn h.rep_nonzero
  exact ⟨Projectivization.mk F v hv,(incident_mk_vector h v hv).mpr hfv⟩

omit [Fintype n] [DecidableEq n] in
theorem point_join_iff_incidence (p q r : Points (F:=F) (n:=n)) :
    p.submodule≤q.submodule ⊔ r.submodule ↔
      ∀h : Hyperplanes (F:=F) (n:=n),Incident q h→Incident r h→Incident p h := by
  let W := q.submodule ⊔ r.submodule
  have hspan : p.submodule≤W ↔ p.rep∈W := by
    rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]
  rw [hspan]
  constructor
  · intro hp h hq hr
    have hW : W≤LinearMap.ker h.rep := by
      apply sup_le
      · rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]
        exact hq
      · rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]
        exact hr
    exact hW hp
  · intro hp
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W p.rep).mp
    intro f hf
    by_cases hf0 : f=0
    · rw [hf0]
      rfl
    · have hq : f q.rep=0 := (Submodule.mem_dualAnnihilator f).mp hf q.rep
        ((show q.submodule≤W from le_sup_left) (by rw [Projectivization.submodule_eq];exact mem_span_singleton_self _))
      have hr : f r.rep=0 := (Submodule.mem_dualAnnihilator f).mp hf r.rep
        ((show r.submodule≤W from le_sup_right) (by rw [Projectivization.submodule_eq];exact mem_span_singleton_self _))
      exact (incident_mk_form p f hf0).mp
        (hp (Projectivization.mk F f hf0) ((incident_mk_form q f hf0).mpr hq)
          ((incident_mk_form r f hf0).mpr hr))

end SymmetricSubgroupAsymptotics.CFSGProjectiveIncidence
