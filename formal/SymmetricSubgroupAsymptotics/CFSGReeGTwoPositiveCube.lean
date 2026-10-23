import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentre
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Cubing in the actual positive Ree group forgets the second and
third free coordinates. Its surviving first-coordinate polynomial is
a permutation, inverse to the actual first torus weight. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCube
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates CFSGReeGTwoPositiveCentre

def cubeScalar (m : ℕ) (a : Field m) : Field m := a^2*alpha m a

def firstWeight (m : ℕ) (a : Field m) : Field m := a^2/alpha m a

theorem chart_cube (m : ℕ) (x : Fin 3→Field m) :
    (fixedPositiveChart m x)^3=centralHom m (Multiplicative.ofAdd (cubeScalar m (x 0))) := by
  rw [pow_succ,pow_two,chart_mul,chart_mul]
  change fixedPositiveChart m (productCoordinates m (productCoordinates m x x) x)=
    fixedPositiveChart m ![0,0,cubeScalar m (x 0)]
  apply congrArg (fixedPositiveChart m)
  have h3 : (3:Field m)=0 := CharP.cast_eq_zero (Field m) 3
  have h2 : (2:Field m)=-1 := by linear_combination h3
  funext i
  fin_cases i <;> simp [productCoordinates,cubeScalar,map_add] <;>
    ring_nf <;> simp [h3,h2]

theorem cubeScalar_firstWeight (m : ℕ) (a : Field m) :
    cubeScalar m (firstWeight m a)=a := by
  by_cases ha : a=0
  · simp [ha,firstWeight,cubeScalar]
  have hα : alpha m a≠0 := by
    intro he
    have h := congrArg (beta m) he
    rw [beta_alpha,map_zero] at h
    exact ha h
  simp only [cubeScalar,firstWeight,map_div₀,map_pow,alpha_twice]
  field_simp [ha,hα] <;> ring

theorem firstWeight_cubeScalar (m : ℕ) (a : Field m) :
    firstWeight m (cubeScalar m a)=a := by
  by_cases ha : a=0
  · simp [ha,firstWeight,cubeScalar]
  have hα : alpha m a≠0 := by
    intro he
    have h := congrArg (beta m) he
    rw [beta_alpha,map_zero] at h
    exact ha h
  simp only [cubeScalar,firstWeight,map_mul,map_pow,alpha_twice]
  field_simp [ha,hα] <;> ring

def cubeScalarEquiv (m : ℕ) : Field m≃Field m where
  toFun := cubeScalar m
  invFun := firstWeight m
  left_inv := firstWeight_cubeScalar m
  right_inv := cubeScalar_firstWeight m

theorem cubeScalar_injective (m : ℕ) : Function.Injective (cubeScalar m) :=
  (cubeScalarEquiv m).injective

theorem cubeScalar_surjective (m : ℕ) : Function.Surjective (cubeScalar m) :=
  (cubeScalarEquiv m).surjective

theorem chart_cube_eq_iff (m : ℕ) (x y : Fin 3→Field m) :
    (fixedPositiveChart m x)^3=(fixedPositiveChart m y)^3 ↔ x 0=y 0 := by
  rw [chart_cube,chart_cube]
  constructor
  · intro h
    exact cubeScalar_injective m (congrArg Multiplicative.toAdd (centralHom_injective m h))
  · intro h
    rw [h]

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCube
