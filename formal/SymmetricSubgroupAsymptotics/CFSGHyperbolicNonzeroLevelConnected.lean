import SymmetricSubgroupAsymptotics.CFSGTwoFunctionalPrescription
import SymmetricSubgroupAsymptotics.CFSGParabolicQuadricCount
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation

/-! Every nonzero level of a split hyperbolic quadratic form is
connected by steps whose differences are singular. Independent positive
projections give a two-step path by two linear prescriptions. Proportional
projections are joined through a third positive direction. Characteristic
two and the binary field are included. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHyperbolicNonzeroLevelConnected
open CFSGParabolicQuadricCount
variable {K I : Type} [Field K] [Fintype I] [DecidableEq I]

theorem dotDual_ne_zero {x : I → K} (hx : x ≠ 0) : dotDual x ≠ 0 := by
  intro he
  apply hx
  funext i
  have hv := LinearMap.congr_fun he (Pi.single i 1)
  change dotProduct x (Pi.single i 1) = 0 at hv
  simpa only [dotProduct_single, mul_one] using hv

theorem dotDual_not_smul {x u : I → K} (hu : u ∉ Submodule.span K {x}) :
    ∀ c : K, dotDual u ≠ c • dotDual x := by
  intro c he
  apply hu
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  funext i
  have hv := LinearMap.congr_fun he (Pi.single i 1)
  change dotProduct u (Pi.single i 1) = c * dotProduct x (Pi.single i 1) at hv
  simpa only [dotProduct_single, mul_one, Pi.smul_apply, smul_eq_mul] using hv.symm

def norm (h : (I → K) × (I → K)) : K := dotProduct h.1 h.2

def Step (c : K) (h k : (I → K) × (I → K)) : Prop :=
  norm h = c ∧ norm k = c ∧ norm (h - k) = 0

theorem connect_independent (c : K) (h k : (I → K) × (I → K))
    (hh : norm h = c) (hk : norm k = c) (hx : h.1 ≠ 0)
    (hu : k.1 ∉ Submodule.span K {h.1}) :
    Relation.ReflTransGen (Step c) h k := by
  obtain ⟨y, hxy, huy⟩ := CFSGTwoFunctionalPrescription.exists_pair_values
    (dotDual h.1) (dotDual k.1) (dotDual_ne_zero hx) (dotDual_not_smul hu)
    c (2 * c - dotProduct h.1 k.2)
  change dotProduct h.1 y = c at hxy
  change dotProduct k.1 y = 2 * c - dotProduct h.1 k.2 at huy
  let z := (h.1, y)
  have hhz : Step c h z := by
    refine ⟨hh, hxy, ?_⟩
    change dotProduct (h.1 - h.1) (h.2 - y) = 0
    rw [sub_self, zero_dotProduct]
  have hzk : Step c z k := by
    refine ⟨hxy, hk, ?_⟩
    change dotProduct (h.1 - k.1) (y - k.2) = 0
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hxy, huy]
    change c - dotProduct h.1 k.2 - (2 * c - dotProduct h.1 k.2 - norm k) = 0
    rw [hk]
    ring
  exact (Relation.ReflTransGen.single hhz).trans (Relation.ReflTransGen.single hzk)

theorem not_mem_span_reverse {x z : I → K} (hx : x ≠ 0)
    (hz : z ∉ Submodule.span K {x}) : x ∉ Submodule.span K {z} := by
  intro hm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have ha0 : a ≠ 0 := by
    intro h
    exact hx (by simpa only [h, zero_smul] using ha.symm)
  apply hz
  apply Submodule.mem_span_singleton.mpr
  refine ⟨a⁻¹, ?_⟩
  rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]

theorem exists_direction_outside (hI : 2 ≤ Fintype.card I) (x : I → K) (hx : x ≠ 0) :
    ∃ j : I, (Pi.single j (1 : K) : I → K) ∉ Submodule.span K {x} := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card I) i
  refine ⟨j, ?_⟩
  intro hm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have hv := congrFun ha i
  change a * x i = (Pi.single j (1 : K) : I → K) i at hv
  have hai : a * x i = 0 := by simpa [Pi.single_apply, hj, Ne.symm hj] using hv
  have ha0 : a = 0 := (mul_eq_zero.mp hai).resolve_right hi
  have he := congrFun ha j
  have hbad : (0 : K) = 1 := by simpa only [ha0, zero_smul, Pi.zero_apply, Pi.single_eq_same] using he
  exact zero_ne_one hbad

theorem connected (hI : 2 ≤ Fintype.card I) (c : K) (hc : c ≠ 0)
    (h k : (I → K) × (I → K)) (hh : norm h = c) (hk : norm k = c) :
    Relation.ReflTransGen (Step c) h k := by
  classical
  have hx : h.1 ≠ 0 := by
    intro hz
    have he : c = 0 := hh.symm.trans (by simp only [norm, hz, zero_dotProduct])
    exact hc he
  have hu : k.1 ≠ 0 := by
    intro hz
    have he : c = 0 := hk.symm.trans (by simp only [norm, hz, zero_dotProduct])
    exact hc he
  by_cases hux : k.1 ∉ Submodule.span K {h.1}
  · exact connect_independent c h k hh hk hx hux
  · have hux' : k.1 ∈ Submodule.span K {h.1} := not_not.mp hux
    obtain ⟨j, hj⟩ := exists_direction_outside hI h.1 hx
    let z : (I → K) × (I → K) := (Pi.single j 1, Pi.single j c)
    have hz : norm z = c := by simp only [norm, z, single_dotProduct, Pi.single_eq_same, one_mul]
    have hzx : z.1 ∉ Submodule.span K {h.1} := hj
    have hxz : h.1 ∉ Submodule.span K {z.1} := not_mem_span_reverse hx hzx
    have huz : k.1 ∉ Submodule.span K {z.1} := by
      intro hm
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hux'
      have ha0 : a ≠ 0 := by
        intro hzero
        exact hu (by simpa only [hzero, zero_smul] using ha.symm)
      apply hxz
      have hv := (Submodule.span K {z.1}).smul_mem a⁻¹ hm
      rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul] at hv
      exact hv
    have hz0 : z.1 ≠ 0 := by
      intro he
      exact hzx (he ▸ (Submodule.span K {h.1}).zero_mem)
    exact (connect_independent c h z hh hz hx hzx).trans
      (connect_independent c z k hz hk hz0 huz)

end SymmetricSubgroupAsymptotics.CFSGHyperbolicNonzeroLevelConnected
