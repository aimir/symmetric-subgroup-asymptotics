import SymmetricSubgroupAsymptotics.CFSGHyperbolicNonzeroLevelConnected
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! At a nonzero dot-product level one can choose an actual mixed
orthogonal probe pair, each pairing nontrivially with the source. The
construction works over the binary field and uses only a nonzero kernel
vector plus the proved two-functional prescription. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGDotProductMixedProbes
open CFSGParabolicQuadricCount CFSGHyperbolicNonzeroLevelConnected
variable {K I : Type} [Field K] [Fintype I] [DecidableEq I]

theorem exists_nonzero_kernel (hI : 2 ≤ Fintype.card I) (f : (I → K) →ₗ[K] K) :
    ∃ z : I → K, z ≠ 0 ∧ f z = 0 := by
  have hr : Module.finrank K f.range ≤ 1 := by
    simpa only [Module.finrank_self] using (Submodule.finrank_le (R := K) f.range)
  have hd := f.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hd
  have hk : 1 ≤ Module.finrank K f.ker := by omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp hk)
  exact ⟨z, hz0, hz⟩

theorem exists_mixed_probes (hI : 2 ≤ Fintype.card I) (x y : I → K)
    (hxy : dotProduct x y ≠ 0) :
    ∃ p q : I → K, dotProduct p q = 0 ∧ dotProduct y p ≠ 0 ∧ dotProduct x q ≠ 0 := by
  classical
  have hyx : dotProduct y x ≠ 0 := by simpa only [dotProduct_comm] using hxy
  have hx : x ≠ 0 := by
    intro he
    exact hxy (by rw [he, zero_dotProduct])
  obtain ⟨z, hz0, hz⟩ := exists_nonzero_kernel hI (dotDual y)
  let p := x + z
  have hyp : dotProduct y p = dotProduct y x := by
    change dotDual y (x + z) = dotDual y x
    rw [map_add, hz, add_zero]
  have hpn : p ∉ Submodule.span K {x} := by
    intro hm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    have he := congrArg (dotDual y) ha
    change dotDual y (a • x) = dotDual y (x + z) at he
    rw [map_smul, map_add, hz, add_zero] at he
    change a * dotProduct y x = dotProduct y x at he
    have ha1 : a = 1 := mul_right_cancel₀ hyx (he.trans (one_mul _).symm)
    have hp : x = x + z := by simpa only [ha1, one_smul] using ha
    exact hz0 ((add_left_cancel ((add_zero x).trans hp)).symm)
  have hp0 : p ≠ 0 := fun he => hpn (he ▸ (Submodule.span K {x}).zero_mem)
  have hxn : x ∉ Submodule.span K {p} := not_mem_span_reverse hx hpn
  obtain ⟨q, hpq, hxq⟩ := CFSGTwoFunctionalPrescription.exists_pair_values
    (dotDual p) (dotDual x) (dotDual_ne_zero hp0) (dotDual_not_smul hxn) 0 1
  refine ⟨p, q, hpq, ?_, ?_⟩
  · exact fun he => hyx (hyp.symm.trans he)
  · change dotDual x q ≠ 0
    rw [hxq]
    exact one_ne_zero

end SymmetricSubgroupAsymptotics.CFSGDotProductMixedProbes
