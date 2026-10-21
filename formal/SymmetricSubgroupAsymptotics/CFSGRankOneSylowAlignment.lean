import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Inner alignment of an actual ordered pair of Sylow subgroups from
an actual rank-one two-cell cover. The adjusted automorphism remains an
automorphism of the original group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGRankOneSylowAlignment

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_inner_fix_pair (P : Sylow p G) (B : Subgroup G) (w : G)
    (hBN : B = Subgroup.normalizer (P : Set G)) (hw : w ∉ B)
    (hcover : ∀ g : G, g ∈ B ∨ ∃ (b : B) (u : P), g=b.val*w*u.val)
    (f : MulAut G) :
    ∃ g : G, (MulAut.conj g*f) • P=P ∧
      (MulAut.conj g*f) • (w • P)=w • P := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq G (f • P) P
  let α : MulAut G := MulAut.conj a*f
  have hα : α • P=P := by
    change (MulAut.conj a*f) • P=P
    rw [mul_smul]
    exact ha
  have hwP : w • P≠P := by
    intro he
    apply hw
    rw [hBN]
    exact Sylow.smul_eq_iff_mem_normalizer.mp he
  have hR : α • (w • P)≠P := by
    intro he
    have hh := congrArg (fun Q : Sylow p G => α⁻¹ • Q) (he.trans hα.symm)
    exact hwP (by simpa only [inv_smul_smul] using hh)
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq G P (α • (w • P))
  have hkB : k ∉ B := by
    intro hkB
    have hkN : k ∈ Subgroup.normalizer (P : Set G) := by rwa [←hBN]
    exact hR (hk.symm.trans (Sylow.smul_eq_iff_mem_normalizer.mpr hkN))
  obtain ⟨b,u,he⟩ := (hcover k).resolve_left hkB
  have hu : (u : G) • P=P :=
    Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer u.property)
  have hb : (b : G) • (w • P)=α • (w • P) := by
    rw [he,mul_smul,mul_smul,hu] at hk
    exact hk
  have hbN : (b : G)⁻¹ ∈ Subgroup.normalizer (P : Set G) := by
    apply (Subgroup.normalizer (P : Set G)).inv_mem
    rw [←hBN]
    exact b.property
  have hbP : (b : G)⁻¹ • P=P := Sylow.smul_eq_iff_mem_normalizer.mpr hbN
  refine ⟨(b : G)⁻¹*a, ?_, ?_⟩
  · change ((MulAut.conj ((b : G)⁻¹*a))*f) • P=P
    rw [map_mul,mul_assoc,mul_smul]
    change (b : G)⁻¹ • (α • P)=P
    rw [hα,hbP]
  · rw [map_mul,mul_assoc,mul_smul]
    change (b : G)⁻¹ • (α • (w • P))=w • P
    rw [←hb,inv_smul_smul]

end SymmetricSubgroupAsymptotics.CFSGRankOneSylowAlignment
