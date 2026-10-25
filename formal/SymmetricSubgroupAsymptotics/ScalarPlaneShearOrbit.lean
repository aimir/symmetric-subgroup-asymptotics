import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Literal upper and lower shears act transitively on nonzero vectors
of a scalar plane. Only three or two displayed elementary operations
are needed; there is no finite action census or group recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarPlaneShearOrbit
variable {K P : Type*} [Field K] [Group P]
variable (ψ : P →* MulAut (Multiplicative (Fin 2 → K)))
variable (hL : ∀ a : K, ∃ g : P, ∀ v : Fin 2 → K,
  ψ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![v 0,a*v 0+v 1])
variable (hU : ∀ a : K, ∃ g : P, ∀ v : Fin 2 → K,
  ψ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![v 0+a*v 1,v 1])

include hL hU

theorem normalize (v : Fin 2 → K) (hv : v ≠ 0) :
    ∃ g : P, ψ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![1,0] := by
  by_cases hx : v 0 = 0
  · have hy : v 1 ≠ 0 := by
      intro hy
      apply hv
      funext i
      fin_cases i
      · exact hx
      · exact hy
    obtain ⟨g,hg⟩ := hU (v 1)⁻¹
    obtain ⟨h,hh⟩ := hL (-v 1)
    have hg' : ψ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![1,v 1] := by
      refine (hg v).trans (congrArg Multiplicative.ofAdd ?_)
      funext i
      fin_cases i
      · change v 0+(v 1)⁻¹*v 1 = 1
        rw [hx,zero_add,inv_mul_cancel₀ hy]
      · rfl
    have hh' : ψ h (Multiplicative.ofAdd ![1,v 1]) = Multiplicative.ofAdd ![1,0] := by
      refine (hh ![1,v 1]).trans (congrArg Multiplicative.ofAdd ?_)
      funext i
      fin_cases i
      · rfl
      · change (-v 1)*1+v 1 = 0
        simp only [mul_one,neg_add_cancel]
    refine ⟨h*g,?_⟩
    rw [map_mul]
    change ψ h (ψ g (Multiplicative.ofAdd v)) = _
    rw [hg',hh']
  · obtain ⟨g,hg⟩ := hL ((1-v 1)/v 0)
    obtain ⟨h,hh⟩ := hU (1-v 0)
    obtain ⟨k,hk⟩ := hL (-1)
    have hg' : ψ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![v 0,1] := by
      refine (hg v).trans (congrArg Multiplicative.ofAdd ?_)
      funext i
      fin_cases i
      · rfl
      · change ((1-v 1)/v 0)*v 0+v 1 = 1
        rw [div_mul_cancel₀ _ hx]
        ring
    have hh' : ψ h (Multiplicative.ofAdd ![v 0,1]) = Multiplicative.ofAdd ![1,1] := by
      refine (hh ![v 0,1]).trans (congrArg Multiplicative.ofAdd ?_)
      funext i
      fin_cases i
      · change v 0+(1-v 0)*1 = 1
        ring
      · rfl
    have hk' : ψ k (Multiplicative.ofAdd ![1,1]) = Multiplicative.ofAdd ![1,0] := by
      refine (hk ![1,1]).trans (congrArg Multiplicative.ofAdd ?_)
      funext i
      fin_cases i
      · rfl
      · change (-1 : K)*1+1 = 0
        ring
    refine ⟨k*h*g,?_⟩
    rw [map_mul,map_mul]
    change ψ k (ψ h (ψ g (Multiplicative.ofAdd v))) = _
    rw [hg',hh',hk']

theorem transitive (v w : Fin 2 → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : P, ψ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd w := by
  obtain ⟨g,hg⟩ := normalize ψ hL hU v hv
  obtain ⟨h,hh⟩ := normalize ψ hL hU w hw
  letI : MulAction P (Multiplicative (Fin 2 → K)) := MulAction.compHom _ ψ
  change g • Multiplicative.ofAdd v = Multiplicative.ofAdd ![1,0] at hg
  change h • Multiplicative.ofAdd w = Multiplicative.ofAdd ![1,0] at hh
  refine ⟨h⁻¹*g,?_⟩
  change (h⁻¹*g) • Multiplicative.ofAdd v = Multiplicative.ofAdd w
  rw [mul_smul,hg,←hh,inv_smul_smul]

end SymmetricSubgroupAsymptotics.ScalarPlaneShearOrbit
