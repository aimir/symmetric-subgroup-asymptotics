import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Quadratic realizations in characteristic two

All nonsingularity hypotheses concern the polar bilinear form itself. No
associated form divided by two is used. Surjective realizations have the
same kernel and differ by a unique actual orthogonal linear automorphism.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {E V : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Actual surjective linear maps realizing the given quadratic form. -/
def QuadraticRealizations (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) :=
  {f : E →ₗ[ZMod 2] V // Function.Surjective f ∧ q.comp f = Q}

/-- The polar radical is exactly the kernel of a surjective realization.
This uses nonsingularity of the target polar form, not the characteristic
zero correspondence with associated bilinear forms. -/
theorem quadraticRealization_kernel (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (f : QuadraticRealizations Q q) : f.1.ker = Q.polarBilin.ker := by
  have hp : Q.polarBilin = LinearMap.compl₁₂ q.polarBilin f.1 f.1 :=
    (congrArg QuadraticMap.polarBilin f.2.2).symm.trans (QuadraticMap.polarBilin_comp q f.1)
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, hp]
  constructor
  · intro hx
    ext y
    change q.polarBilin (f.1 x) (f.1 y) = 0
    simp [hx]
  · intro hx
    apply hq
    intro y
    obtain ⟨z, rfl⟩ := f.2.1 y
    exact congrArg (fun l : E →ₗ[ZMod 2] ZMod 2 => l z) hx

/-- Any two surjective realizations therefore have the same literal kernel. -/
theorem quadraticRealization_same_kernel (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (f g : QuadraticRealizations Q q) : f.1.ker = g.1.ker := by
  rw [quadraticRealization_kernel Q q hq f, quadraticRealization_kernel Q q hq g]

private def realizationLinearEquiv (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (f g : QuadraticRealizations Q q) : V ≃ₗ[ZMod 2] V :=
  (f.1.quotKerEquivOfSurjective f.2.1).symm.trans
    ((Submodule.quotEquivOfEq _ _ (quadraticRealization_same_kernel Q q hq f g)).trans
      (g.1.quotKerEquivOfSurjective g.2.1))

private theorem realizationLinearEquiv_apply (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (f g : QuadraticRealizations Q q) (x : E) :
    realizationLinearEquiv Q q hq f g (f.1 x) = g.1 x := by
  simp only [realizationLinearEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The unique target isometry carrying one realization to the other. -/
def quadraticRealizationIsometry (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (f g : QuadraticRealizations Q q) : q.IsometryEquiv q where
  toLinearEquiv := realizationLinearEquiv Q q hq f g
  map_app' y := by
    obtain ⟨x, rfl⟩ := f.2.1 y
    change q (realizationLinearEquiv Q q hq f g (f.1 x)) = q (f.1 x)
    rw [realizationLinearEquiv_apply]
    exact (congrArg (fun t : QuadraticForm (ZMod 2) E => t x) g.2.2).trans
      (congrArg (fun t : QuadraticForm (ZMod 2) E => t x) f.2.2).symm

@[simp] theorem quadraticRealizationIsometry_apply (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (f g : QuadraticRealizations Q q) (x : E) :
    quadraticRealizationIsometry Q q hq f g (f.1 x) = g.1 x :=
  realizationLinearEquiv_apply Q q hq f g x

/-- The map between any two realizations is unique, so the torsor assertion
has no stabilizer or multiplicity assumption hidden in it. -/
theorem quadraticRealizationIsometry_unique (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (f g : QuadraticRealizations Q q) (e : q.IsometryEquiv q)
    (he : ∀ x, e (f.1 x) = g.1 x) : e = quadraticRealizationIsometry Q q hq f g := by
  apply DFunLike.ext
  intro y
  obtain ⟨x, rfl⟩ := f.2.1 y
  exact (he x).trans (quadraticRealizationIsometry_apply Q q hq f g x).symm

private def isometryRealization (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (f : QuadraticRealizations Q q)
    (e : q.IsometryEquiv q) : QuadraticRealizations Q q :=
  ⟨e.toLinearEquiv.toLinearMap.comp f.1,
    e.toLinearEquiv.surjective.comp f.2.1, by
      ext x
      exact (e.map_app (f.1 x)).trans
        (congrArg (fun t : QuadraticForm (ZMod 2) E => t x) f.2.2)⟩

/-- A chosen realization identifies the entire fibre with the actual
orthogonal isometry type. If no realization exists the fibre is empty. -/
def quadraticRealizationEquiv (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (f : QuadraticRealizations Q q) : QuadraticRealizations Q q ≃ q.IsometryEquiv q where
  toFun g := quadraticRealizationIsometry Q q hq f g
  invFun e := isometryRealization Q q f e
  left_inv g := by
    apply Subtype.ext
    ext x
    exact quadraticRealizationIsometry_apply Q q hq f g x
  right_inv e := by
    apply DFunLike.ext
    intro y
    obtain ⟨x, rfl⟩ := f.2.1 y
    exact quadraticRealizationIsometry_apply Q q hq f (isometryRealization Q q f e) x

/-- Nonempty realization fibres have exactly the orthogonal-group cardinal. -/
theorem quadraticRealization_card (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (f : QuadraticRealizations Q q) :
    Nat.card (QuadraticRealizations Q q) = Nat.card (q.IsometryEquiv q) :=
  Nat.card_congr (quadraticRealizationEquiv Q q hq f)

/-- The uniform realization bound includes the empty fibre. -/
theorem quadraticRealization_card_le (Q : QuadraticForm (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft) :
    Nat.card (QuadraticRealizations Q q) ≤ Nat.card (q.IsometryEquiv q) := by
  classical
  by_cases h : Nonempty (QuadraticRealizations Q q)
  · exact (quadraticRealization_card Q q hq h.some).le
  · letI : IsEmpty (QuadraticRealizations Q q) := not_nonempty_iff.mp h
    simp

/-- The two-dimensional hyperbolic form, explicitly `x₀x₁`. -/
def hyperbolicQuadraticTwo : QuadraticForm (ZMod 2) (Fin 2 → ZMod 2) :=
  QuadraticMap.proj 0 1

/-- The four-dimensional hyperbolic form, explicitly `x₀x₁+x₂x₃`. -/
def hyperbolicQuadraticFour : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2) :=
  QuadraticMap.proj 0 1 + QuadraticMap.proj 2 3

@[simp] theorem hyperbolicQuadraticTwo_apply (x : Fin 2 → ZMod 2) :
    hyperbolicQuadraticTwo x = x 0 * x 1 := rfl

@[simp] theorem hyperbolicQuadraticFour_apply (x : Fin 4 → ZMod 2) :
    hyperbolicQuadraticFour x = x 0 * x 1 + x 2 * x 3 := rfl

end SymmetricSubgroupAsymptotics
