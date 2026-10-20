import SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases

/-! Four-point coordinate gauges, independent of any original group
census. The joint equation retains the actual order-three element and
its actual inverting involution; it is the fixed-fibre gauge for the
sixteen-point normalizer construction. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourLocalCubicPointGauge
open BinaryFourBlockAugmentation

def pointDecidableEq (x y : Local) : Decidable (x = y) :=
  if h : x 0 = y 0 ∧ x 1 = y 1 then
    isTrue (by funext i; fin_cases i; exact h.1; exact h.2)
  else isFalse (fun hxy => h ⟨congrFun hxy 0, congrFun hxy 1⟩)

local instance : DecidableEq Local := pointDecidableEq
local instance : Fintype (Equiv.Perm Local) := Equiv.instFintype
local instance : DecidableEq (Equiv.Perm Local) := Fintype.decidableEqEquivFintype

def reflection : Equiv.Perm Local where
  toFun v i := v (Equiv.swap 0 1 i)
  invFun v i := v (Equiv.swap 0 1 i)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pointEquiv : Fin 4 ≃ Local where
  toFun := ![0, ![1,0], ![0,1], ![1,1]]
  invFun v := if v 0 = 0 then (if v 1 = 0 then 0 else 2)
    else (if v 1 = 0 then 1 else 3)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def candidateFin (j : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := ![![0,1,2,3],![0,1,3,2],![0,2,1,3],![0,2,3,1],![0,3,1,2],![0,3,2,1],![1,0,2,3],![1,0,3,2],![1,2,0,3],![1,2,3,0],![1,3,0,2],![1,3,2,0],![2,0,1,3],![2,0,3,1],![2,1,0,3],![2,1,3,0],![2,3,0,1],![2,3,1,0],![3,0,1,2],![3,0,2,1],![3,1,0,2],![3,1,2,0],![3,2,0,1],![3,2,1,0]] j
  invFun := ![![0,1,2,3],![0,1,3,2],![0,2,1,3],![0,3,1,2],![0,2,3,1],![0,3,2,1],![1,0,2,3],![1,0,3,2],![2,0,1,3],![3,0,1,2],![2,0,3,1],![3,0,2,1],![1,2,0,3],![1,3,0,2],![2,1,0,3],![3,1,0,2],![2,3,0,1],![3,2,0,1],![1,2,3,0],![1,3,2,0],![2,1,3,0],![3,1,2,0],![2,3,1,0],![3,2,1,0]] j
  left_inv := by revert j; decide +kernel
  right_inv := by revert j; decide +kernel

def candidate (j : Fin 24) : Equiv.Perm Local :=
  pointEquiv.symm.trans ((candidateFin j).trans pointEquiv)

theorem cubic_gauge (c : Equiv.Perm Local) (hc : c^3 = 1) (hne : c ≠ 1) :
    ∃ e : Equiv.Perm Local, e * c * e⁻¹ = localCycle.toEquiv := by
  have finite : ∀ c : Equiv.Perm Local, c^3 = 1 → c ≠ 1 →
      ∃ j : Fin 24, ∀ v : Local, candidate j (c v) = localCycle (candidate j v) := by
    decide +kernel
  obtain ⟨j,hj⟩ := finite c hc hne
  refine ⟨candidate j, ?_⟩
  apply Equiv.ext
  intro v
  change candidate j (c ((candidate j).symm v)) = localCycle v
  simpa only [Equiv.apply_symm_apply] using hj ((candidate j).symm v)

theorem cubic_involution_gauge (c t : Equiv.Perm Local)
    (hc : c^3 = 1) (hne : c ≠ 1) (ht : t^2 = 1)
    (hconj : t * c * t⁻¹ = c⁻¹) :
    ∃ e : Equiv.Perm Local,
      e * c * e⁻¹ = localCycle.toEquiv ∧ e * t * e⁻¹ = reflection := by
  have finite : ∀ c t : Equiv.Perm Local,
      c^3 = 1 → c ≠ 1 → t^2 = 1 → t*c*t⁻¹ = c⁻¹ →
      ∃ j : Fin 24,
        (∀ v : Local, candidate j (c v) = localCycle (candidate j v)) ∧
        (∀ v : Local, candidate j (t v) = reflection (candidate j v)) := by
    decide +kernel
  obtain ⟨j,hc',ht'⟩ := finite c t hc hne ht hconj
  refine ⟨candidate j, ?_, ?_⟩
  · apply Equiv.ext
    intro v
    change candidate j (c ((candidate j).symm v)) = localCycle v
    simpa only [Equiv.apply_symm_apply] using hc' ((candidate j).symm v)
  · apply Equiv.ext
    intro v
    change candidate j (t ((candidate j).symm v)) = reflection v
    simpa only [Equiv.apply_symm_apply] using ht' ((candidate j).symm v)

end SymmetricSubgroupAsymptotics.BinaryFourLocalCubicPointGauge
