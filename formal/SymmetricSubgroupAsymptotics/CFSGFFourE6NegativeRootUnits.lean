import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOpposition
import Mathlib.Tactic.Group

/-! Actual integral Geck opposition transports the folded positive-root
product to the negative roots. No faithfulness or recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NegativeRootUnits
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckFieldOpposition

private theorem integral_opposition (i : Fin 4) :
    CFSGGeckIntegralMatrices.Omega E6Base*integerE i*
      CFSGGeckIntegralMatrices.Omega E6Base=integerF i := by
  have hh (j : Fin 6) : CFSGGeckIntegralMatrices.Omega E6Base*e6EZ j*
      CFSGGeckIntegralMatrices.Omega E6Base=e6FZ j :=
    omega_E CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base (E6Index j)
  fin_cases i
  · change CFSGGeckIntegralMatrices.Omega E6Base*(e6EZ 0+e6EZ 5)*
      CFSGGeckIntegralMatrices.Omega E6Base=e6FZ 0+e6FZ 5
    simp only [mul_add,add_mul,hh]
  · change CFSGGeckIntegralMatrices.Omega E6Base*(e6EZ 2+e6EZ 4)*
      CFSGGeckIntegralMatrices.Omega E6Base=e6FZ 2+e6FZ 4
    simp only [mul_add,add_mul,hh]
  · exact hh 3
  · exact hh 1

theorem folded_opposition (K : Type*) [CommRing K] (i : Fin 4) (t : K) :
    oppositionUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K*
      canonicalRoot realizationData K false i t*
      (oppositionUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K)⁻¹=
        canonicalRoot realizationData K true i t := by
  have hroot : fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K*
      fieldRoot realizationData K false i*
      fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K=
        fieldRoot realizationData K true i := by
    change (Int.castRingHom K).mapMatrix (CFSGGeckIntegralMatrices.Omega E6Base)*
      (Int.castRingHom K).mapMatrix (integerE i)*
      (Int.castRingHom K).mapMatrix (CFSGGeckIntegralMatrices.Omega E6Base)=
        (Int.castRingHom K).mapMatrix (integerF i)
    rw [←map_mul,←map_mul,integral_opposition]
  have hsecond : fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K*
      fieldSecond realizationData K false i*
      fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K=
        fieldSecond realizationData K true i := by
    change (Int.castRingHom K).mapMatrix (CFSGGeckIntegralMatrices.Omega E6Base)*
      (Int.castRingHom K).mapMatrix (positiveSecondZ i)*
      (Int.castRingHom K).mapMatrix (CFSGGeckIntegralMatrices.Omega E6Base)=
        (Int.castRingHom K).mapMatrix (negativeSecondZ i)
    rw [←map_mul,←map_mul]
    rfl
  apply Units.ext
  change fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K*
      (1+t • fieldRoot realizationData K false i+t^2 • fieldSecond realizationData K false i)*
      fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K=
        1+t • fieldRoot realizationData K true i+t^2 • fieldSecond realizationData K true i
  simp only [mul_add,add_mul,mul_one,smul_mul_assoc,mul_smul_comm,
    fieldOmega_square,hroot,hsecond]

theorem folded_negative_root (K : Type*) [CommRing K] (i : Fin 4) (t : K) :
    canonicalRoot realizationData K true i t=
      ![canonicalRoot e6Data K true 0 t*canonicalRoot e6Data K true 5 t,
        canonicalRoot e6Data K true 2 t*canonicalRoot e6Data K true 4 t,
        canonicalRoot e6Data K true 3 t,canonicalRoot e6Data K true 1 t] i := by
  let O := oppositionUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K
  have hE (j : Fin 6) : O*canonicalRoot e6Data K false j t*O⁻¹=
      canonicalRoot e6Data K true j t :=
    canonicalRoot_conjugate CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index K false j t
  have hF : O*canonicalRoot realizationData K false i t*O⁻¹=
      canonicalRoot realizationData K true i t := folded_opposition K i t
  rw [←hF,folded_positive_root]
  fin_cases i
  · change O*(canonicalRoot e6Data K false 0 t*canonicalRoot e6Data K false 5 t)*O⁻¹=_
    calc
      _=(O*canonicalRoot e6Data K false 0 t*O⁻¹)*
          (O*canonicalRoot e6Data K false 5 t*O⁻¹) := by group
      _=_ := by rw [hE,hE]; rfl
  · change O*(canonicalRoot e6Data K false 2 t*canonicalRoot e6Data K false 4 t)*O⁻¹=_
    calc
      _=(O*canonicalRoot e6Data K false 2 t*O⁻¹)*
          (O*canonicalRoot e6Data K false 4 t*O⁻¹) := by group
      _=_ := by rw [hE,hE]; rfl
  · exact hE 3
  · exact hE 1

end SymmetricSubgroupAsymptotics.CFSGFFourE6NegativeRootUnits
