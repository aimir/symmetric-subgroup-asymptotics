import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! Additivity determines a plane homomorphism from its two actual axis
sections. The coefficients need not be assumed scalar-linear elsewhere. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.ScalarPlaneAxisHom

theorem apply_of_axis_values {K : Type*} [Semiring K]
    (f : Multiplicative (Fin 2 → K) →* Multiplicative (Fin 2 → K)) (a b : K)
    (h0 : ∀ t, f (Multiplicative.ofAdd ![t,0]) = Multiplicative.ofAdd ![0,b*t])
    (h1 : ∀ t, f (Multiplicative.ofAdd ![0,t]) = Multiplicative.ofAdd ![a*t,0])
    (v : Fin 2 → K) :
    f (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![a*v 1,b*v 0] := by
  have hv : v = ![v 0,0]+![0,v 1] := by
    funext i
    fin_cases i
    · change v 0 = v 0+0
      exact (add_zero _).symm
    · change v 1 = 0+v 1
      exact (zero_add _).symm
  calc
    f (Multiplicative.ofAdd v) =
        f (Multiplicative.ofAdd ![v 0,0]*Multiplicative.ofAdd ![0,v 1]) :=
      congrArg f ((congrArg Multiplicative.ofAdd hv).trans (ofAdd_add _ _))
    _ = f (Multiplicative.ofAdd ![v 0,0])*f (Multiplicative.ofAdd ![0,v 1]) := map_mul _ _ _
    _ = Multiplicative.ofAdd (![0,b*v 0]+![a*v 1,0]) := by rw [h0,h1,ofAdd_add]
    _ = Multiplicative.ofAdd ![a*v 1,b*v 0] := by
      apply congrArg Multiplicative.ofAdd
      funext i
      fin_cases i
      · change 0+a*v 1 = a*v 1
        exact zero_add _
      · change b*v 0+0 = b*v 0
        exact add_zero _

end SymmetricSubgroupAsymptotics.ScalarPlaneAxisHom
