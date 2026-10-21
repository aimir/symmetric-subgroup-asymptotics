import SymmetricSubgroupAsymptotics.CFSGProjectiveIncidence
import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates

/-! A permutation of original points with a matching incidence-preserving
permutation of original hyperplanes is a genuine projective collineation.
The point permutation also determines the hyperplane permutation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveIncidenceCollineation
open Module LinearMap Submodule CFSGProjectiveIncidence
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem hyperplane_eq_of_incident_iff (h k : Hyperplanes (F:=F) (n:=n))
    (he : ∀p : Points (F:=F) (n:=n),Incident p h↔Incident p k) : h=k := by
  have hk : LinearMap.ker h.rep=LinearMap.ker k.rep := by
    ext v
    by_cases hv : v=0
    · subst v
      simp only [LinearMap.mem_ker,map_zero]
    · exact ((incident_mk_vector h v hv).symm.trans
        ((he (Projectivization.mk F v hv)).trans (incident_mk_vector k v hv)))
  obtain ⟨a,ha⟩ := CFSGTypeARootMembership.exists_unit_smul_of_ker_eq h.rep_nonzero k.rep_nonzero hk
  apply Projectivization.submodule_injective
  rw [Projectivization.submodule_eq,Projectivization.submodule_eq]
  exact (Submodule.span_singleton_eq_span_singleton.mpr ⟨a,ha.symm⟩).symm

theorem point_permutation_mem_collineationGroup
    (e : Equiv.Perm (Points (F:=F) (n:=n)))
    (d : Equiv.Perm (Hyperplanes (F:=F) (n:=n)))
    (hi : ∀p h,Incident (e p) (d h)↔Incident p h) :
    e∈CFSGProjectiveFrameCoordinates.collineationGroup (F:=F) (n:=n) := by
  intro p q r
  change (e p).submodule≤(e q).submodule ⊔ (e r).submodule ↔
    p.submodule≤q.submodule ⊔ r.submodule
  rw [point_join_iff_incidence,point_join_iff_incidence]
  constructor
  · intro h k hq hr
    exact (hi p k).mp (h (d k) ((hi q k).mpr hq) ((hi r k).mpr hr))
  · intro h k hq hr
    obtain ⟨j,rfl⟩ := d.surjective k
    exact (hi p j).mpr (h j ((hi q j).mp hq) ((hi r j).mp hr))

theorem hyperplane_permutation_unique
    (e : Equiv.Perm (Points (F:=F) (n:=n)))
    (d d' : Equiv.Perm (Hyperplanes (F:=F) (n:=n)))
    (hi : ∀p h,Incident (e p) (d h)↔Incident p h)
    (hi' : ∀p h,Incident (e p) (d' h)↔Incident p h) : d=d' := by
  apply Equiv.ext
  intro h
  apply hyperplane_eq_of_incident_iff
  intro p
  obtain ⟨q,rfl⟩ := e.surjective p
  exact (hi q h).trans (hi' q h).symm

end SymmetricSubgroupAsymptotics.CFSGProjectiveIncidenceCollineation
