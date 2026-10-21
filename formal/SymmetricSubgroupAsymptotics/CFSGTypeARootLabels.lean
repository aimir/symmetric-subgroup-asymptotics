import SymmetricSubgroupAsymptotics.CFSGTypeAHyperplaneMembership
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! Faithful original projective point and hyperplane labels for root
groups. Equality is detected by the actual centre line or form kernel,
so arbitrary representatives introduce no extra group-model assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootLabels
open Matrix Module LinearMap Submodule CFSGTypeAProjectivePointRoots CFSGTypeAHyperplaneRoots
open CFSGTypeARootMembership
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem exists_nonzero_point_form (hn : 2≤Fintype.card n) {v : n→F} (hv : v≠0) :
    ∃f : Dual F (n→F),f≠0 ∧ f v=0 := by
  have hd : 0<Module.finrank F (pointForms v) := by
    have hh := pointForms_finrank_add_one hv
    omega
  letI : Nontrivial (pointForms v) := Module.nontrivial_of_finrank_pos hd
  obtain ⟨f,hf⟩ := exists_ne (0 : pointForms v)
  refine ⟨f.val,?_,f.property⟩
  intro he
  exact hf (Subtype.ext he)

theorem exists_nonzero_kernel_vector (hn : 2≤Fintype.card n) {f : Dual F (n→F)} (hf : f≠0) :
    ∃v : n→F,v≠0 ∧ f v=0 := by
  have hd : 0<Module.finrank F (LinearMap.ker f) := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    rw [Module.finrank_fintype_fun_eq_card] at hh
    omega
  letI : Nontrivial (LinearMap.ker f) := Module.nontrivial_of_finrank_pos hd
  obtain ⟨v,hv⟩ := exists_ne (0 : LinearMap.ker f)
  refine ⟨v.val,?_,v.property⟩
  intro he
  exact hv (Subtype.ext he)

private theorem pointRoot_le_of_centre_eq (hn : 3≤Fintype.card n)
    {v w : n→F} (hv : v≠0) (hc : (F ∙ v)=(F ∙ w)) : pointRoot v≤pointRoot w := by
  rintro x ⟨f,rfl⟩
  by_cases hf : f.toAdd.val=0
  · have hz : f=1 := congrArg Multiplicative.ofAdd (Subtype.ext hf)
    rw [hz,map_one]
    exact (pointRoot w).one_mem
  · exact (pointRoot_mem_iff_centre hn f.toAdd.property hf hv).mpr hc

theorem pointRoot_eq_iff_centre (hn : 3≤Fintype.card n) {v w : n→F} (hv : v≠0) (hw : w≠0) :
    pointRoot v=pointRoot w ↔ (F ∙ v)=(F ∙ w) := by
  constructor
  · intro he
    obtain ⟨f,hf,hfv⟩ := exists_nonzero_point_form (by omega) hv
    have hx : projection (transvectionSL hfv)∈pointRoot v :=
      ⟨Multiplicative.ofAdd ⟨f,hfv⟩,rfl⟩
    rw [he] at hx
    exact (pointRoot_mem_iff_centre hn hfv hf hv).mp hx
  · intro hc
    exact le_antisymm (pointRoot_le_of_centre_eq hn hv hc)
      (pointRoot_le_of_centre_eq hn hw hc.symm)

private theorem hyperplaneRoot_le_of_axis_eq (hn : 3≤Fintype.card n)
    {f g : Dual F (n→F)} (hf : f≠0) (hg : g≠0) (he : LinearMap.ker f=LinearMap.ker g) :
    hyperplaneRoot f≤hyperplaneRoot g := by
  rintro x ⟨v,rfl⟩
  by_cases hv : v.toAdd.val=0
  · have hz : v=1 := congrArg Multiplicative.ofAdd (Subtype.ext hv)
    rw [hz,map_one]
    exact (hyperplaneRoot g).one_mem
  · exact (hyperplaneRoot_mem_iff_axis hn v.toAdd.property hf hg hv).mpr he

theorem hyperplaneRoot_eq_iff_axis (hn : 3≤Fintype.card n)
    {f g : Dual F (n→F)} (hf : f≠0) (hg : g≠0) :
    hyperplaneRoot f=hyperplaneRoot g ↔ LinearMap.ker f=LinearMap.ker g := by
  constructor
  · intro he
    obtain ⟨v,hv,hfv⟩ := exists_nonzero_kernel_vector (by omega) hf
    have hx : projection (transvectionSL hfv)∈hyperplaneRoot f :=
      ⟨Multiplicative.ofAdd ⟨v,hfv⟩,rfl⟩
    rw [he] at hx
    exact (hyperplaneRoot_mem_iff_axis hn hfv hf hg hv).mp hx
  · intro he
    exact le_antisymm (hyperplaneRoot_le_of_axis_eq hn hf hg he)
      (hyperplaneRoot_le_of_axis_eq hn hg hf he.symm)

def pointLabel (p : ℙ F (n→F)) : Subgroup (PSL (F:=F) (n:=n)) := pointRoot p.rep

def hyperplaneLabel (p : ℙ F (Dual F (n→F))) : Subgroup (PSL (F:=F) (n:=n)) :=
  hyperplaneRoot p.rep

theorem pointLabel_injective (hn : 3≤Fintype.card n) : Function.Injective (pointLabel (F:=F) (n:=n)) := by
  intro p q he
  apply Projectivization.submodule_injective
  rw [Projectivization.submodule_eq,Projectivization.submodule_eq]
  exact (pointRoot_eq_iff_centre hn p.rep_nonzero q.rep_nonzero).mp he

theorem hyperplaneLabel_injective (hn : 3≤Fintype.card n) :
    Function.Injective (hyperplaneLabel (F:=F) (n:=n)) := by
  intro p q he
  have hk := (hyperplaneRoot_eq_iff_axis hn p.rep_nonzero q.rep_nonzero).mp he
  obtain ⟨a,ha⟩ := exists_unit_smul_of_ker_eq p.rep_nonzero q.rep_nonzero hk
  apply Projectivization.submodule_injective
  rw [Projectivization.submodule_eq,Projectivization.submodule_eq]
  exact (Submodule.span_singleton_eq_span_singleton.mpr ⟨a,ha.symm⟩).symm

end SymmetricSubgroupAsymptotics.CFSGTypeARootLabels
