import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalExchange
import SymmetricSubgroupAsymptotics.CFSGHermitianSingularRay
import SymmetricSubgroupAsymptotics.CFSGLinearFunctionalKernelScalar

/-! Fixed actual singular points determine restricted Hermitian
functional kernels. Proportionality retains the genuine field
involution on the first vector variable. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem singularPoint_nonzero (P : SingularPoint sigma H) :
    ∃ x ∈ P.val, x ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp (by rw [P.property.1]))

theorem singularPoint_span (P : SingularPoint sigma H) (x : I → K)
    (hx : x ∈ P.val) (hx0 : x ≠ 0) : P.val = K ∙ x := by
  have hle : K ∙ x ≤ P.val := (Submodule.span_singleton_le_iff_mem _ _).mpr hx
  exact (Submodule.eq_of_le_of_finrank_le hle
    (by rw [P.property.1, finrank_span_singleton hx0])).symm

theorem orthogonal_iff_singular_representatives (P Q : SingularPoint sigma H)
    (x y : I → K) (hx : x ∈ P.val) (hy : y ∈ Q.val) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    Orthogonal sigma H P.val Q.val ↔ hermitianPair sigma H x y = 0 := by
  constructor
  · exact fun h => h x hx y hy
  · intro h u hu v hv
    rw [singularPoint_span sigma H P x hx hx0] at hu
    rw [singularPoint_span sigma H Q y hy hy0] at hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [hermitianPair_smul, h, mul_zero]

def restrictedHermitianPairing (S : IsotropicSpace sigma H) (x : I → K) : S.val →ₗ[K] K :=
  (pairRightLinear sigma H x).comp S.val.subtype

theorem restrictedHermitianPairing_ker_eq
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (S : IsotropicSpace sigma H)
    (hfix : ∀ Q : SingularPoint sigma H, Q.val ≤ S.val → f Q = Q)
    (P : SingularPoint sigma H) (x y : I → K)
    (hx : x ∈ P.val) (hy : y ∈ (f P).val) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    (restrictedHermitianPairing sigma H S x).ker = (restrictedHermitianPairing sigma H S y).ker := by
  ext w
  change hermitianPair sigma H x w.val = 0 ↔ hermitianPair sigma H y w.val = 0
  by_cases hw : w.val = 0
  · simp only [hw, pair_zero_right]
  let Q := singularRay sigma H w.val hw (S.property w.val w.property w.val w.property)
  have hQ : Q.val ≤ S.val := (Submodule.span_singleton_le_iff_mem _ _).mpr w.property
  have hwQ : w.val ∈ Q.val := Submodule.mem_span_singleton_self _
  have h := hf P Q
  rw [hfix Q hQ] at h
  exact (orthogonal_iff_singular_representatives sigma H P Q x w.val hx hwQ hx0 hw).symm.trans
    (h.symm.trans (orthogonal_iff_singular_representatives sigma H (f P) Q y w.val hy hwQ hy0 hw))

theorem restrictedHermitianPairing_proportional
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (S : IsotropicSpace sigma H)
    (hfix : ∀ Q : SingularPoint sigma H, Q.val ≤ S.val → f Q = Q)
    (P : SingularPoint sigma H) (x y : I → K)
    (hx : x ∈ P.val) (hy : y ∈ (f P).val) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hn : restrictedHermitianPairing sigma H S x ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ restrictedHermitianPairing sigma H S y = c • restrictedHermitianPairing sigma H S x :=
  CFSGLinearFunctionalKernelScalar.exists_ne_zero_smul_of_ker_eq _ _
    (restrictedHermitianPairing_ker_eq sigma H f hf S hfix P x y hx hy hx0 hy0) hn

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
