import SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
import SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernelScalar

/-! Fixing the actual projective points of a singular subspace forces
the corresponding restricted polar functionals to be proportional.
The kernel equality is derived from literal orthogonality incidence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (B : LinearMap.BilinForm K V)

theorem zeroOn_iff_representatives (P Q : Points B) (x y : V)
    (hx : x∈P.val) (hy : y∈Q.val) (hx0 : x≠0) (hy0 : y≠0) :
    ZeroOn B P.val Q.val ↔ B x y=0 := by
  constructor
  · exact fun h=>h x hx y hy
  · intro h u hu v hv
    rw [←point_span B P x hx hx0] at hu
    rw [←point_span B Q y hy hy0] at hv
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp only [map_smul,LinearMap.smul_apply,h,smul_zero]

def restrictedPairing (W : Subspaces B) (x : V) : W.val→ₗ[K]K :=
  (B x).comp W.val.subtype

theorem restrictedPairing_ker_eq (f : Points B≃Points B)
    (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)
    (W : Subspaces B) (hfix : ∀Q : Points B,Q.val≤W.val → f Q=Q)
    (P : Points B) (x y : V) (hx : x∈P.val) (hy : y∈(f P).val)
    (hx0 : x≠0) (hy0 : y≠0) :
    (restrictedPairing B W x).ker=(restrictedPairing B W y).ker := by
  ext w
  change B x w.val=0 ↔ B y w.val=0
  by_cases hw : w.val=0
  · simp only [hw,map_zero]
  let Q := ray B w.val hw (W.property w.val w.property w.val w.property)
  have hQ : Q.val≤W.val := (Submodule.span_singleton_le_iff_mem _ _).mpr w.property
  have hwQ : w.val∈Q.val := Submodule.mem_span_singleton_self _
  have hfQ := hfix Q hQ
  have h := horth P Q
  rw [hfQ] at h
  exact (zeroOn_iff_representatives B P Q x w.val hx hwQ hx0 hw).symm.trans
    (h.symm.trans (zeroOn_iff_representatives B (f P) Q y w.val hy hwQ hy0 hw))

theorem restrictedPairing_proportional (f : Points B≃Points B)
    (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)
    (W : Subspaces B) (hfix : ∀Q : Points B,Q.val≤W.val → f Q=Q)
    (P : Points B) (x y : V) (hx : x∈P.val) (hy : y∈(f P).val)
    (hx0 : x≠0) (hy0 : y≠0) (hn : restrictedPairing B W x≠0) :
    ∃c : K,c≠0 ∧ restrictedPairing B W y=c•restrictedPairing B W x :=
  CFSGLinearFunctionalKernelScalar.exists_ne_zero_smul_of_ker_eq _ _
    (restrictedPairing_ker_eq B f horth W hfix P x y hx hy hx0 hy0) hn

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
