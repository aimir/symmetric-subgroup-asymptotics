import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCube

/-! Reparameterizing the actual squared torus by the cube polynomial
makes its first free weight a literal square. The other two weights
are the nonlinear scalars used in the additive rigidity certificates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoSquareWeightCoordinates
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalTorus
open CFSGReeGTwoPositiveCube CFSGReeGTwoFixedTorusAction
open CFSGGTwoNaturalPositiveTorusAction CFSGReeGTwoPositiveDerived
open CFSGReeGTwoOriginalPositiveSubgroup

def cubeUnit (m : ℕ) (r : (Field m)ˣ) : (Field m)ˣ := r^2*unitsAlpha m r

theorem cubeUnit_val (m : ℕ) (r : (Field m)ˣ) :
    (cubeUnit m r:Field m)=cubeScalar m (r:Field m) := rfl

theorem cubeUnit_square (m : ℕ) (r : (Field m)ˣ) :
    (cubeUnit m r)^2=cubeUnit m (r^2) := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val,cubeUnit_val,cubeScalar,map_pow]
  ring

theorem first_weight (m : ℕ) (r : (Field m)ˣ) :
    (rootScale (Field m) (cubeUnit m r,unitsAlpha m (cubeUnit m r)) 0:Field m)=r := by
  simp only [rootScale,Units.val_mul,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val]
  rw [unitsAlpha_val,cubeUnit_val]
  simpa only [firstWeight,div_eq_mul_inv] using firstWeight_cubeScalar m (r:Field m)

theorem middle_weight (m : ℕ) (r : (Field m)ˣ) :
    (rootScale (Field m) (cubeUnit m r,unitsAlpha m (cubeUnit m r)) 2:Field m)=
      (r:Field m)*alpha m r := by
  simp only [rootScale,Units.val_mul,Units.val_inv_eq_inv_val]
  rw [unitsAlpha_val,cubeUnit_val]
  have hα : alpha m (r:Field m)≠0 := by
    simpa only [unitsAlpha_val] using (unitsAlpha m r).ne_zero
  simp only [cubeScalar,map_mul,map_pow,alpha_twice]
  field_simp [r.ne_zero,hα] <;> ring

theorem last_weight (m : ℕ) (r : (Field m)ˣ) :
    (rootScale (Field m) (cubeUnit m r,unitsAlpha m (cubeUnit m r)) 3:Field m)=
      cubeScalar m r := rfl

def squareCoordinates (m : ℕ) (r : (Field m)ˣ) (x : Fin 3→Field m) : Fin 3→Field m :=
  ![x 0*(r:Field m)^2,x 1*((r:Field m)*alpha m r)^2,
    x 2*cubeScalar m ((r:Field m)^2)]

theorem fixedScale_square_cubeUnit (m : ℕ) (r : (Field m)ˣ) (x : Fin 3→Field m) :
    fixedScaleCoordinates m ((cubeUnit m r)^2) x=squareCoordinates m r x := by
  rw [cubeUnit_square]
  funext i
  fin_cases i <;>
    simp [fixedScaleCoordinates,squareCoordinates,first_weight,middle_weight,last_weight,map_pow,mul_pow]

theorem torusAut_square_cubeUnit_apply (m : ℕ) (r : (Field m)ˣ) (x : Fin 3→Field m) :
    fixedPositiveTorusAut m ((cubeUnit m r)^2) (fixedPositiveChart m x)=
      fixedPositiveChart m (squareCoordinates m r x) := by
  apply Subtype.ext
  exact (fixedTorus_fixedWord m ((cubeUnit m r)^2) x).trans
    (congrArg (CFSGReeGTwoOriginalFixedWordChart.fixedWord m)
      (fixedScale_square_cubeUnit m r x))

end SymmetricSubgroupAsymptotics.CFSGReeGTwoSquareWeightCoordinates
