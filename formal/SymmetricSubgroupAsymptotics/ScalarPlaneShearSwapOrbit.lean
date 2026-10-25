import SymmetricSubgroupAsymptotics.ScalarPlaneShearOrbit
import Mathlib.Tactic.FieldSimp

/-! One literal shear family and an actual primitive axis swap suffice
for a nonzero plane orbit. Conjugation constructs the opposite shear;
no named linear-group recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarPlaneShearSwapOrbit
variable {K P : Type*} [Field K] [Group P]
variable (ψ : P →* MulAut (Multiplicative (Fin 2 → K)))
variable (hL : ∀ c : K, ∃ g : P, ∀ v : Fin 2 → K,
  ψ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![v 0,c*v 0+v 1])
variable (w : P) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
variable (hw : ∀ v : Fin 2 → K,
  ψ w (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![a*v 1,b*v 0])

include hL w a b ha hb hw

theorem upper_shears (t : K) : ∃ g : P, ∀ v : Fin 2 → K,
    ψ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![v 0+t*v 1,v 1] := by
  obtain ⟨g,hg⟩ := hL (t*b/a)
  refine ⟨w*g*w⁻¹,?_⟩
  intro v
  let z : Fin 2 → K := ![v 1/b,v 0/a]
  have hwz : ψ w (Multiplicative.ofAdd z) = Multiplicative.ofAdd v := by
    refine (hw z).trans (congrArg Multiplicative.ofAdd ?_)
    funext i
    fin_cases i
    · change a*(v 0/a) = v 0
      field_simp [ha]
    · change b*(v 1/b) = v 1
      field_simp [hb]
  have hc : ψ (w*g*w⁻¹) (ψ w (Multiplicative.ofAdd z)) =
      ψ w (ψ g (Multiplicative.ofAdd z)) := by
    rw [map_mul,map_mul,map_inv]
    change ψ w (ψ g ((ψ w).symm (ψ w (Multiplicative.ofAdd z)))) = _
    rw [MulEquiv.symm_apply_apply]
  calc
    _ = ψ w (ψ g (Multiplicative.ofAdd z)) := by rw [←hwz]; exact hc
    _ = ψ w (Multiplicative.ofAdd ![z 0,(t*b/a)*z 0+z 1]) := congrArg (ψ w) (hg z)
    _ = Multiplicative.ofAdd ![a*((t*b/a)*z 0+z 1),b*z 0] := hw _
    _ = Multiplicative.ofAdd ![v 0+t*v 1,v 1] := by
      apply congrArg Multiplicative.ofAdd
      funext i
      fin_cases i
      · change a*((t*b/a)*(v 1/b)+v 0/a) = v 0+t*v 1
        field_simp [ha,hb] <;> ring
      · change b*(v 1/b) = v 1
        field_simp [hb]

theorem transitive (v v' : Fin 2 → K) (hv : v ≠ 0) (hv' : v' ≠ 0) :
    ∃ g : P, ψ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd v' :=
  ScalarPlaneShearOrbit.transitive ψ hL (upper_shears ψ hL w a b ha hb hw) v v' hv hv'

end SymmetricSubgroupAsymptotics.ScalarPlaneShearSwapOrbit
