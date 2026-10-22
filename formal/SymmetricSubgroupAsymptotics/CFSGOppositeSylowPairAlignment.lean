import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Subgroup.Map

/-! Inner adjustment fixes an actual ordered opposite Sylow pair whenever
its positive normalizer is transitive on the disjoint Sylow conjugates.
This does not require a rank-one two-cell decomposition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGOppositeSylowPairAlignment
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_inner_fix_pair (P Q : Sylow p G)
    (hPQ : (P : Subgroup G)⊓(Q : Subgroup G)=⊥)
    (halign : ∀g : G,(P : Subgroup G)⊓
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom=⊥→
        ∃b∈Subgroup.normalizer (P : Set G),
          (P : Subgroup G).map (MulAut.conj g).toMonoidHom=
            (Q : Subgroup G).map (MulAut.conj b).toMonoidHom)
    (f : MulAut G) :
    ∃g : G,(MulAut.conj g*f) • P=P ∧ (MulAut.conj g*f) • Q=Q := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq G (f • P) P
  let α : MulAut G := MulAut.conj a*f
  have hα : α • P=P := by
    change (MulAut.conj a*f) • P=P
    rw [mul_smul]
    exact ha
  have hαmap : (P : Subgroup G).map α.toMonoidHom=(P : Subgroup G) :=
    congrArg (fun R : Sylow p G=>(R : Subgroup G)) hα
  have hR : (P : Subgroup G)⊓(α • Q : Subgroup G)=⊥ := by
    have hh := congrArg (fun S : Subgroup G=>S.map α.toMonoidHom) hPQ
    dsimp only at hh
    rw [Subgroup.map_inf _ _ _ α.injective,Subgroup.map_bot,hαmap] at hh
    exact hh
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq G P (α • Q)
  have hkmap : (P : Subgroup G).map (MulAut.conj k).toMonoidHom=
      (α • Q : Subgroup G) :=
    congrArg (fun R : Sylow p G=>(R : Subgroup G)) hk
  rw [←hkmap] at hR
  obtain ⟨b,hbN,hb⟩ := halign k hR
  have hbQ : b • Q=α • Q := by
    apply Sylow.ext
    exact hb.symm.trans hkmap
  have hbP : b⁻¹ • P=P := Sylow.smul_eq_iff_mem_normalizer.mpr
    ((Subgroup.normalizer (P : Set G)).inv_mem hbN)
  refine ⟨b⁻¹*a,?_,?_⟩
  · rw [map_mul,mul_assoc,mul_smul]
    change b⁻¹ • (α • P)=P
    rw [hα,hbP]
  · rw [map_mul,mul_assoc,mul_smul]
    change b⁻¹ • (α • Q)=Q
    rw [←hbQ,inv_smul_smul]

end SymmetricSubgroupAsymptotics.CFSGOppositeSylowPairAlignment
