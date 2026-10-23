import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGTrialityNormTorusScalars
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-! Literal cross-actions of the two relative simple torus words.
The short word contributes the actual cubic Frobenius norm on the
middle parameter. The middle word scales the short parameter inversely
when its scalar belongs to the literal fixed field. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMixedTorusConjugation
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortParameterWeyl
open CFSGTrialityFixedWeylWords
open CFSGTrialityGeckShortTorusConjugation CFSGNormTwoGeckTorusConjugation
open CFSGNormTwoGeckParameterizedTorus CFSGSerreQuadraticMatrix
open CFSGIntegerMatrixPairing CFSGTrialityFixedField CFSGSerreOrdinaryTwists
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

def middleTorus (K : Type) [Field K] (a : Kˣ) : (Matrix GeckIndex GeckIndex K)ˣ :=
  parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 1 a

private theorem middle_outer_pairing (i : Fin 3) :
    integerPairing (CartanMatrix.D 4) (Index 1 : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)).val (Index (outerNode i) : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)).val = -1 := by
  change integerPairing (CartanMatrix.D 4)
    (Pi.single 1 (1:ℤ) : Fin 4→ℤ) (Pi.single (outerNode i) (1:ℤ) : Fin 4→ℤ) = -1
  fin_cases i <;> decide

private theorem outer_middle_pairing (i : Fin 3) :
    integerPairing (CartanMatrix.D 4) (Index (outerNode i) : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)).val (Index 1 : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)).val = -1 := by
  change integerPairing (CartanMatrix.D 4)
    (Pi.single (outerNode i) (1:ℤ) : Fin 4→ℤ) (Pi.single 1 (1:ℤ) : Fin 4→ℤ) = -1
  fin_cases i <;> decide

private theorem middle_outer_root (K : Type) [Field K] (a : Kˣ) (i : Fin 3) (t : K) :
    middleTorus K a*canonicalRoot rawData K false (outerNode i) t*(middleTorus K a)⁻¹ =
      canonicalRoot rawData K false (outerNode i) (t*(a:K)⁻¹) := by
  have he := torus_conjugate_positive (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 1 (outerNode i) a t
  rw [middle_outer_pairing] at he
  simpa only [zpow_neg_one] using he

private theorem outer_middle_root (K : Type) [Field K] (a : Kˣ) (i : Fin 3) (t : K) :
    parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K (outerNode i) a*
        canonicalRoot rawData K false 1 t*
    (parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K (outerNode i) a)⁻¹ =
        canonicalRoot rawData K false 1 (t*(a:K)⁻¹) := by
  have he := torus_conjugate_positive (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K (outerNode i) 1 a t
  rw [outer_middle_pairing] at he
  simpa only [zpow_neg_one] using he

theorem middleTorus_middle (K : Type) [Field K] (a : Kˣ) (t : K) :
    middleTorus K a*canonicalRoot rawData K false 1 t*(middleTorus K a)⁻¹ =
      canonicalRoot rawData K false 1 (t*(a:K)^2) := by
  have he := torus_conjugate_positive (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 1 1 a t
  have hpair : integerPairing (CartanMatrix.D 4) (Index 1 : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)).val (Index 1 : CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)).val = 2 := by
    change integerPairing (CartanMatrix.D 4)
      (Pi.single 1 (1:ℤ) : Fin 4→ℤ) (Pi.single 1 (1:ℤ) : Fin 4→ℤ) = 2
    decide
  rw [hpair] at he
  simpa only [zpow_ofNat] using he

theorem middleTorus_short (K : Type) [Field K] (sigma : K≃+*K)
    (a : Kˣ) (ha : sigma (a:K)=(a:K)) (t : K) :
    middleTorus K a*shortOrbit K sigma false t*(middleTorus K a)⁻¹ =
      shortOrbit K sigma false (t*(a:K)⁻¹) := by
  let T := middleTorus K a
  have h0 : outerNode (0:Fin 3)=(0:Fin 4) := rfl
  have h1 : outerNode (1:Fin 3)=(2:Fin 4) := rfl
  have h2 : outerNode (2:Fin 3)=(3:Fin 4) := rfl
  calc
    _ = (T*canonicalRoot rawData K false (outerNode 0) t*T⁻¹)*
        (T*canonicalRoot rawData K false (outerNode 1) (sigma t)*T⁻¹)*
        (T*canonicalRoot rawData K false (outerNode 2) (sigma (sigma t))*T⁻¹) := by
      simp only [T,shortOrbit,h0,h1,h2]
      group
    _ = _ := by
      dsimp only [T]
      rw [middle_outer_root,middle_outer_root,middle_outer_root]
      simp only [shortOrbit,h0,h1,h2,map_mul,map_inv₀,ha]

theorem shortTorus_middle (K : Type) [Field K] (sigma : K≃+*K)
    (c : Kˣ) (t : K) :
    shortTorusWord K sigma c*canonicalRoot rawData K false 1 t*
      (shortTorusWord K sigma c)⁻¹ =
        canonicalRoot rawData K false 1
          (t*((c:K)*sigma (c:K)*sigma (sigma (c:K)))⁻¹) := by
  rw [shortTorusWord_eq_product]
  let T (i : Fin 3) := parameterTorus (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K (outerNode i) (outerParameters K sigma c i)
  change (T 0*T 1*T 2)*canonicalRoot rawData K false 1 t*(T 0*T 1*T 2)⁻¹ = _
  calc
    _ = T 0*(T 1*(T 2*canonicalRoot rawData K false 1 t*(T 2)⁻¹)*(T 1)⁻¹)*(T 0)⁻¹ := by group
    _ = _ := by
      dsimp only [T]
      rw [outer_middle_root,outer_middle_root,outer_middle_root]
      congr 1
      simp only [outerParameters,Matrix.cons_val_zero,mul_inv_rev]
      ac_rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMixedTorusConjugation
