import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalSingularGallery
import Mathlib.Tactic.Push

/-! An actual maximal singular space cannot be perpendicular to an
external singular vector. In particular disjoint maximal singular spaces
pair nondegenerately. This uses inclusion maximality and the quadratic
zero condition, without a split ambient dimension or a characteristic guard. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalCrossPairing
open CFSGQuadraticMaximalSingularGallery
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_nonorthogonal (Q : QuadraticForm K V)
    (P : Submodule K V) (hP : MaximalSingular Q P) (v : V)
    (hv : Q v = 0) (hvn : v ∉ P) : ∃ w ∈ P, Q.polarBilin v w ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hs : ∀ x ∈ P ⊔ Submodule.span K {v}, Q x = 0 := by
    intro x hx
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have huv : Q.polarBilin u v = 0 := (QuadraticMap.polar_comm Q u v).trans (h u hu)
    rw [QuadraticMap.map_add Q u (a • v)]
    change Q u + Q (a • v) + Q.polarBilin u (a • v) = 0
    rw [hP.1 u hu, Q.map_smul, hv, smul_zero, map_smul, huv, smul_zero,
      add_zero, add_zero]
  have he := hP.2 (P ⊔ Submodule.span K {v}) hs le_sup_left
  have hm : v ∈ P ⊔ Submodule.span K {v} :=
    (show Submodule.span K {v} ≤ P ⊔ Submodule.span K {v} from le_sup_right)
      (Submodule.mem_span_singleton_self v)
  exact hvn (he ▸ hm)

theorem exists_pairing_one (Q : QuadraticForm K V)
    (P : Submodule K V) (hP : MaximalSingular Q P) (v : V)
    (hv : Q v = 0) (hvn : v ∉ P) : ∃ w ∈ P, Q v = 0 ∧ Q w = 0 ∧ Q.polarBilin v w = 1 := by
  obtain ⟨w, hw, hB⟩ := exists_nonorthogonal Q P hP v hv hvn
  refine ⟨(Q.polarBilin v w)⁻¹ • w, P.smul_mem _ hw, hv, ?_, ?_⟩
  · rw [Q.map_smul, hP.1 w hw, smul_zero]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hB]

theorem opposed_pairing_one (Q : QuadraticForm K V)
    (P R : Submodule K V) (hP : MaximalSingular Q P) (hR : MaximalSingular Q R)
    (hdis : Disjoint P R) (v : V) (hv : v ∈ P) (hv0 : v ≠ 0) :
    ∃ w ∈ R, Q w = 0 ∧ Q.polarBilin v w = 1 := by
  have hvn : v ∉ R := by
    intro hRmem
    exact hv0 ((Submodule.disjoint_def.mp hdis) v hv hRmem)
  obtain ⟨w, hw, _, hwQ, hB⟩ := exists_pairing_one Q R hR v (hP.1 v hv) hvn
  exact ⟨w, hw, hwQ, hB⟩

end SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalCrossPairing
