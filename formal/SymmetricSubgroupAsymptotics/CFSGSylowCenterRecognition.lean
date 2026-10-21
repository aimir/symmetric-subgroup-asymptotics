import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Center

/-! The union of the centres of Sylow p-subgroups is intrinsically
preserved by every automorphism of a finite group. Actual-model proofs
may identify this set with their concrete root elements; this generic
result makes no such identification by definition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSylowCenterRecognition
variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

def sylowCenterElements : Set G :=
  {x | ∃P : Sylow p G,∃z : P,z∈Subgroup.center P ∧ (z : G)=x}

theorem automorphism_mem_sylowCenterElements (f : MulAut G) {x : G}
    (hx : x∈sylowCenterElements (G:=G) p) : f x∈sylowCenterElements (G:=G) p := by
  obtain ⟨P,z,hz,rfl⟩ := hx
  let Q : Sylow p G := P.mapSurjective (f:=f.toMonoidHom) f.surjective
  let e : P≃*Q := f.subgroupMap (P : Subgroup G)
  refine ⟨Q,e z,?_,rfl⟩
  exact (Subgroup.centerCongr e ⟨z,hz⟩).property

theorem automorphism_mem_sylowCenterElements_iff (f : MulAut G) (x : G) :
    f x∈sylowCenterElements (G:=G) p ↔ x∈sylowCenterElements (G:=G) p := by
  constructor
  · intro hx
    have hh := automorphism_mem_sylowCenterElements p f.symm hx
    simpa only [f.symm_apply_apply] using hh
  · exact automorphism_mem_sylowCenterElements p f

end SymmetricSubgroupAsymptotics.CFSGSylowCenterRecognition
