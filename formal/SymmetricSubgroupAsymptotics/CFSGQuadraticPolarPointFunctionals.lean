import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
import SymmetricSubgroupAsymptotics.CFSGSingularPlaneTriangle
import SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernelScalar

/-! Fixing the actual projective points of a Q-singular subspace forces
the corresponding restricted polar functionals to be proportional.
The kernel equality is derived from literal orthogonality incidence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (q : QuadraticForm K V)

theorem zeroOn_iff_representatives (P Q : Points q) (x y : V)
    (hx : x∈P.val) (hy : y∈Q.val) (hx0 : x≠0) (hy0 : y≠0) :
    ZeroOn q.polarBilin P.val Q.val ↔ q.polarBilin x y=0 := by
  constructor
  · exact fun h=>h x hx y hy
  · intro h u hu v hv
    rw [←point_span q P x hx hx0] at hu
    rw [←point_span q Q y hy hy0] at hv
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp only [map_smul,LinearMap.smul_apply,h,smul_zero]

def restrictedPairing (W : Subspaces q) (x : V) : W.val→ₗ[K]K :=
  (q.polarBilin x).comp W.val.subtype

theorem restrictedPairing_ker_eq (f : Points q≃Points q)
    (horth : ∀P Q,ZeroOn q.polarBilin (f P).val (f Q).val ↔ ZeroOn q.polarBilin P.val Q.val)
    (W : Subspaces q) (hfix : ∀Q : Points q,Q.val≤W.val → f Q=Q)
    (P : Points q) (x y : V) (hx : x∈P.val) (hy : y∈(f P).val)
    (hx0 : x≠0) (hy0 : y≠0) :
    (restrictedPairing q W x).ker=(restrictedPairing q W y).ker := by
  ext w
  change q.polarBilin x w.val=0 ↔ q.polarBilin y w.val=0
  by_cases hw : w.val=0
  · simp only [hw,map_zero]
  let Q := ray q w.val hw (W.property w.val w.property)
  have hQ : Q.val≤W.val := (Submodule.span_singleton_le_iff_mem _ _).mpr w.property
  have hwQ : w.val∈Q.val := Submodule.mem_span_singleton_self _
  have hfQ := hfix Q hQ
  have h := horth P Q
  rw [hfQ] at h
  exact (zeroOn_iff_representatives q P Q x w.val hx hwQ hx0 hw).symm.trans
    (h.symm.trans (zeroOn_iff_representatives q (f P) Q y w.val hy hwQ hy0 hw))

theorem restrictedPairing_proportional (f : Points q≃Points q)
    (horth : ∀P Q,ZeroOn q.polarBilin (f P).val (f Q).val ↔ ZeroOn q.polarBilin P.val Q.val)
    (W : Subspaces q) (hfix : ∀Q : Points q,Q.val≤W.val → f Q=Q)
    (P : Points q) (x y : V) (hx : x∈P.val) (hy : y∈(f P).val)
    (hx0 : x≠0) (hy0 : y≠0) (hn : restrictedPairing q W x≠0) :
    ∃c : K,c≠0 ∧ restrictedPairing q W y=c•restrictedPairing q W x :=
  CFSGLinearFunctionalKernelScalar.exists_ne_zero_smul_of_ker_eq _ _
    (restrictedPairing_ker_eq q f horth W hfix P x y hx hy hx0 hy0) hn

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
