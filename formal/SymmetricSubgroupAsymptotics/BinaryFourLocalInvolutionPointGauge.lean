import SymmetricSubgroupAsymptotics.BinaryFourLocalCubicPointGauge

/-! The moving-fibre gauges distinguish translations (no fixed point)
from odd affine involutions (a fixed point). Only four points are checked. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourLocalInvolutionPointGauge
open BinaryFourBlockAugmentation

local instance : DecidableEq Local := BinaryFourLocalCubicPointGauge.pointDecidableEq
local instance : Fintype (Equiv.Perm Local) := Equiv.instFintype
local instance : DecidableEq (Equiv.Perm Local) := Fintype.decidableEqEquivFintype

def translation : Equiv.Perm Local where
  toFun v := v + ![1,0]
  invFun v := v + ![1,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem translation_gauge (t : Equiv.Perm Local) (ht : t^2 = 1)
    (hfree : ∀ v : Local, t v ≠ v) :
    ∃ e : Equiv.Perm Local, e * t * e⁻¹ = translation := by
  have finite : ∀ t : Equiv.Perm Local, t^2 = 1 → (∀ v : Local, t v ≠ v) →
      ∃ j : Fin 24, ∀ v : Local,
        BinaryFourLocalCubicPointGauge.candidate j (t v) =
          translation (BinaryFourLocalCubicPointGauge.candidate j v) := by
    decide +kernel
  obtain ⟨j,hj⟩ := finite t ht hfree
  refine ⟨BinaryFourLocalCubicPointGauge.candidate j, ?_⟩
  apply Equiv.ext
  intro v
  change BinaryFourLocalCubicPointGauge.candidate j
      (t ((BinaryFourLocalCubicPointGauge.candidate j).symm v)) = translation v
  simpa only [Equiv.apply_symm_apply] using
    hj ((BinaryFourLocalCubicPointGauge.candidate j).symm v)

theorem reflection_gauge (t : Equiv.Perm Local) (ht : t^2 = 1) (hne : t ≠ 1)
    (hfixed : ∃ v : Local, t v = v) :
    ∃ e : Equiv.Perm Local,
      e * t * e⁻¹ = BinaryFourLocalCubicPointGauge.reflection := by
  have finite : ∀ t : Equiv.Perm Local, t^2 = 1 → t ≠ 1 →
      (∃ i : Fin 4, t (BinaryFourLocalCubicPointGauge.pointEquiv i) =
        BinaryFourLocalCubicPointGauge.pointEquiv i) →
      ∃ j : Fin 24, ∀ v : Local,
        BinaryFourLocalCubicPointGauge.candidate j (t v) =
          BinaryFourLocalCubicPointGauge.reflection
            (BinaryFourLocalCubicPointGauge.candidate j v) := by
    decide +kernel
  have hfixed' : ∃ i : Fin 4, t (BinaryFourLocalCubicPointGauge.pointEquiv i) =
      BinaryFourLocalCubicPointGauge.pointEquiv i := by
    obtain ⟨v,hv⟩ := hfixed
    obtain ⟨i,rfl⟩ := BinaryFourLocalCubicPointGauge.pointEquiv.surjective v
    exact ⟨i,hv⟩
  obtain ⟨j,hj⟩ := finite t ht hne hfixed'
  refine ⟨BinaryFourLocalCubicPointGauge.candidate j, ?_⟩
  apply Equiv.ext
  intro v
  change BinaryFourLocalCubicPointGauge.candidate j
      (t ((BinaryFourLocalCubicPointGauge.candidate j).symm v)) =
        BinaryFourLocalCubicPointGauge.reflection v
  simpa only [Equiv.apply_symm_apply] using
    hj ((BinaryFourLocalCubicPointGauge.candidate j).symm v)

end SymmetricSubgroupAsymptotics.BinaryFourLocalInvolutionPointGauge
