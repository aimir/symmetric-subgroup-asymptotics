import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The literal quadratic forms with a fixed polar form over a field of
order two form a torsor for the dual vector space. Pullback has the SAME
dual linear part and an explicitly retained translation. No quadratic
type, orbit classification or equality of forms from their polars is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryQuadraticRefinementTorsor

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]

private theorem square_eq_self (hK : Nat.card K = 2) (a : K) : a * a = a := by
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 2 := by simpa only [Nat.card_eq_fintype_card] using hK
  simpa only [hc, pow_two] using FiniteField.pow_card a

abbrev Refinement (Q₀ : QuadraticForm K V) :=
  {Q : QuadraticForm K V // Q.polarBilin = Q₀.polarBilin}

/-- The difference is linear, not identified with zero. -/
def difference (hK : Nat.card K = 2) (Q₀ : QuadraticForm K V)
    (Q : Refinement Q₀) : Module.Dual K V where
  toFun x := Q.val x - Q₀ x
  map_add' x y := by
    have hp : Q.val (x + y) - Q.val x - Q.val y =
        Q₀ (x + y) - Q₀ x - Q₀ y :=
      congrArg (fun B : LinearMap.BilinForm K V => B x y) Q.property
    linear_combination hp
  map_smul' a x := by
    simp only [QuadraticMap.map_smul, square_eq_self hK, smul_eq_mul,
      RingHom.id_apply, mul_sub]

/-- A dual vector gives its actual quadratic perturbation. -/
def linearQuadratic (_hK : Nat.card K = 2) (f : Module.Dual K V) :
    QuadraticForm K V := QuadraticMap.linMulLin f f

theorem linearQuadratic_apply (hK : Nat.card K = 2)
    (f : Module.Dual K V) (x : V) : linearQuadratic hK f x = f x := by
  exact square_eq_self hK (f x)

theorem linearQuadratic_polar (hK : Nat.card K = 2)
    (f : Module.Dual K V) : (linearQuadratic hK f).polarBilin = 0 := by
  apply LinearMap.ext₂
  intro x y
  change linearQuadratic hK f (x + y) - linearQuadratic hK f x -
    linearQuadratic hK f y = 0
  simp only [linearQuadratic_apply, map_add]
  abel

def translate (hK : Nat.card K = 2) (Q₀ : QuadraticForm K V)
    (f : Module.Dual K V) : Refinement Q₀ :=
  ⟨Q₀ + linearQuadratic hK f, by
    apply LinearMap.ext₂
    intro x y
    change (Q₀ + linearQuadratic hK f) (x + y) -
        (Q₀ + linearQuadratic hK f) x - (Q₀ + linearQuadratic hK f) y =
      Q₀ (x + y) - Q₀ x - Q₀ y
    simp only [QuadraticMap.add_apply, linearQuadratic_apply, map_add]
    abel⟩

def refinementEquivDual (hK : Nat.card K = 2) (Q₀ : QuadraticForm K V) :
    Refinement Q₀ ≃ Module.Dual K V where
  toFun := difference hK Q₀
  invFun := translate hK Q₀
  left_inv Q := by
    apply Subtype.ext
    apply QuadraticMap.ext
    intro x
    change Q₀ x + linearQuadratic hK (difference hK Q₀ Q) x = Q.val x
    rw [linearQuadratic_apply]
    change Q₀ x + (Q.val x - Q₀ x) = Q.val x
    abel
  right_inv f := by
    apply LinearMap.ext
    intro x
    change (Q₀ + linearQuadratic hK f) x - Q₀ x = f x
    rw [QuadraticMap.add_apply, linearQuadratic_apply]
    abel

def pullback (Q₀ : QuadraticForm K V) (T : V ≃ₗ[K] V)
    (hT : ∀ x y : V, Q₀.polarBilin (T x) (T y) = Q₀.polarBilin x y)
    (Q : Refinement Q₀) : Refinement Q₀ :=
  ⟨Q.val.comp T.toLinearMap, by
    rw [QuadraticMap.polarBilin_comp, Q.property]
    exact LinearMap.ext₂ hT⟩

theorem pullback_affine (hK : Nat.card K = 2) (Q₀ : QuadraticForm K V)
    (T : V ≃ₗ[K] V)
    (hT : ∀ x y : V, Q₀.polarBilin (T x) (T y) = Q₀.polarBilin x y)
    (Q : Refinement Q₀) :
    refinementEquivDual hK Q₀ (pullback Q₀ T hT Q) =
      difference hK Q₀ (pullback Q₀ T hT ⟨Q₀, rfl⟩) +
        (refinementEquivDual hK Q₀ Q).comp T.toLinearMap := by
  apply LinearMap.ext
  intro x
  change Q.val (T x) - Q₀ x =
    (Q₀ (T x) - Q₀ x) + (Q.val (T x) - Q₀ (T x))
  abel

omit [Finite K] in
theorem pullback_fixed_iff (Q₀ : QuadraticForm K V) (T : V ≃ₗ[K] V)
    (hT : ∀ x y : V, Q₀.polarBilin (T x) (T y) = Q₀.polarBilin x y)
    (Q : Refinement Q₀) :
    pullback Q₀ T hT Q = Q ↔ ∀ x : V, Q.val (T x) = Q.val x := by
  constructor
  · intro h x
    exact congrArg (fun R : Refinement Q₀ => R.val x) h
  · intro h
    exact Subtype.ext (QuadraticMap.ext h)

end SymmetricSubgroupAsymptotics.BinaryQuadraticRefinementTorsor
