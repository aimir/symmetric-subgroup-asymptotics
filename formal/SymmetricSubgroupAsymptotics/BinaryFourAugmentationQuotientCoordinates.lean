import SymmetricSubgroupAsymptotics.BinaryFourAugmentationActions
import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds

/-! The elementary quotient coordinates after removing the diagonal.
The two explicit cyclic-module generators work in both dimensions. -/

set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourBlockAugmentation

abbrev TailCoordinates := Fin 4 → Scalar

def tailSpace (full : Bool) : Submodule Scalar TailCoordinates where
  carrier := {x | full = false → x 3 = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy h; simp [hx h, hy h]
  smul_mem' := by intro a x hx h; simp [hx h]

def tail (x : Coordinates) : TailCoordinates := ![x 2, x 3, x 4, x 5]

def tailMap (full : Bool) : space full →ₗ[Scalar] tailSpace full where
  toFun x := ⟨tail x, x.property⟩
  map_add' x y := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  map_smul' a x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

def tailSection (full : Bool) (w : tailSpace full) : space full :=
  ⟨![0, 0, (w : TailCoordinates) 0, (w : TailCoordinates) 1,
    (w : TailCoordinates) 2, (w : TailCoordinates) 3], w.property⟩

theorem tailMap_section (full : Bool) (w : tailSpace full) :
    tailMap full (tailSection full w) = w := by
  apply Subtype.ext
  ext i
  fin_cases i <;> rfl

def tailCycle (full : Bool) : tailSpace full ≃ₗ[Scalar] tailSpace full where
  toFun w := ⟨![(w : TailCoordinates) 2, (w : TailCoordinates) 0 + (w : TailCoordinates) 3,
    (w : TailCoordinates) 1 + (w : TailCoordinates) 3, (w : TailCoordinates) 3], w.property⟩
  invFun w := ⟨![(w : TailCoordinates) 1 + (w : TailCoordinates) 3,
    (w : TailCoordinates) 2 + (w : TailCoordinates) 3,
    (w : TailCoordinates) 0, (w : TailCoordinates) 3], w.property⟩
  left_inv w := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel, mul_zero, add_zero]
  right_inv w := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel, mul_zero, add_zero]
  map_add' x y := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> ring

theorem tailCycle_cube (full : Bool) : tailCycle full ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [tailCycle, pow_succ] <;> ring_nf <;>
    simp only [show (2 : Scalar) = 0 from by decide +kernel, mul_zero, add_zero]

abbrev QuotientVector (full : Bool) := tailSpace full × Local

def quotientCycle (full : Bool) : QuotientVector full ≃ₗ[Scalar] QuotientVector full :=
  (tailCycle full).prodCongr localCycle

theorem quotientCycle_cube (full : Bool) : quotientCycle full ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun f : tailSpace full ≃ₗ[Scalar] tailSpace full => f x.1)
      (tailCycle_cube full)
  · exact congrArg (fun f : Local ≃ₗ[Scalar] Local => f x.2) localCycle_cube

def quotientLinear (full : Bool) :
    Ternary →* (QuotientVector full ≃ₗ[Scalar] QuotientVector full) :=
  powersHom 3 (quotientCycle full) (quotientCycle_cube full)

abbrev QuotientModel (full : Bool) :=
  LinearSemidirectCoprimeSocleBounds.Model (quotientLinear full)

theorem quotientLinear_apply (full : Bool) (z : Ternary) (w : QuotientVector full) :
    quotientLinear full z w =
      ((tailCycle full ^ z.toAdd.val) w.1,
       (kleinCyclicAction z (Multiplicative.ofAdd w.2)).toAdd) := by
  change (quotientCycle full ^ z.toAdd.val) w =
    ((tailCycle full ^ z.toAdd.val) w.1,
      ((localCycle.toAddEquiv.toMultiplicative ^ z.toAdd.val)
        (Multiplicative.ofAdd w.2)).toAdd)
  generalize z.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', LinearEquiv.mul_apply, MulAut.mul_apply]
      rw [ih]
      rfl

theorem tailMap_action (full : Bool) (r : Complement) (x : space full) :
    tailMap full (restrictedLinear full r x) =
      (tailCycle full ^ r.right.toAdd.val) (tailMap full x) := by
  apply Subtype.ext
  change tail ((c ^ r.right.toAdd.val) (x : Coordinates)) =
    (((tailCycle full ^ r.right.toAdd.val) (tailMap full x)) : TailCoordinates)
  generalize r.right.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change ![(c ^ n) x 4, (c ^ n) x 2 + (c ^ n) x 5,
        (c ^ n) x 3 + (c ^ n) x 5, (c ^ n) x 5] = _
      have hi (i : Fin 4) := congrFun ih i
      ext i
      fin_cases i
      · exact hi 2
      · exact congrArg₂ (· + ·) (hi 0) (hi 3)
      · exact congrArg₂ (· + ·) (hi 1) (hi 3)
      · exact hi 3

def quotientGenerator (full : Bool) : Fin 2 → QuotientVector full :=
  ![(⟨![1, 0, 0, 0], by intro h; rfl⟩, 0),
    (⟨![0, 0, 0, if full then 1 else 0], by
      intro h; subst full; rfl⟩, ![1, 0])]

def generatorCoefficients (full : Bool) (w : QuotientVector full) : Fin 6 → Scalar :=
  let a₀ := (w.1 : TailCoordinates) 3 + w.2 1
  let a₁ := (w.1 : TailCoordinates) 3 + w.2 0 + w.2 1
  let a₂ := (w.1 : TailCoordinates) 3 + w.2 0
  let f : Scalar := if full then 1 else 0
  ![(w.1 : TailCoordinates) 0 + f * a₂, (w.1 : TailCoordinates) 1 + f * (a₁ + a₂),
    (w.1 : TailCoordinates) 2 + f * a₁, a₀, a₁, a₂]

theorem quotient_orbit_decomposition (full : Bool) (w : QuotientVector full) :
    w =
      generatorCoefficients full w 0 • quotientGenerator full 0 +
      generatorCoefficients full w 1 • quotientCycle full (quotientGenerator full 0) +
      generatorCoefficients full w 2 • (quotientCycle full ^ 2) (quotientGenerator full 0) +
      generatorCoefficients full w 3 • quotientGenerator full 1 +
      generatorCoefficients full w 4 • quotientCycle full (quotientGenerator full 1) +
      generatorCoefficients full w 5 • (quotientCycle full ^ 2) (quotientGenerator full 1) := by
  rcases w with ⟨⟨x, hx⟩, p⟩
  cases full
  · have hx3 : x 3 = 0 := hx rfl
    apply Prod.ext
    · apply Subtype.ext
      ext i
      fin_cases i <;>
        simp [generatorCoefficients, quotientGenerator, quotientCycle, tailCycle,
          localCycle, pow_two, hx3] <;> ring_nf <;>
        simp only [show (2 : Scalar) = 0 from by decide +kernel,
          show (4 : Scalar) = 0 from by decide +kernel,
          mul_zero, add_zero, zero_add]
    · ext i
      fin_cases i <;>
        simp [generatorCoefficients, quotientGenerator, quotientCycle, tailCycle,
          localCycle, pow_two, hx3] <;> ring_nf <;>
        simp only [show (2 : Scalar) = 0 from by decide +kernel,
          show (4 : Scalar) = 0 from by decide +kernel,
          mul_zero, add_zero, zero_add]
  · apply Prod.ext
    · apply Subtype.ext
      ext i
      fin_cases i <;>
        simp [generatorCoefficients, quotientGenerator, quotientCycle, tailCycle,
          localCycle, pow_two] <;> ring_nf <;>
        simp only [show (2 : Scalar) = 0 from by decide +kernel,
          show (3 : Scalar) = 1 from by decide +kernel,
          show (4 : Scalar) = 0 from by decide +kernel,
          mul_zero, mul_one, add_zero, zero_add]
    · ext i
      fin_cases i <;>
        simp [generatorCoefficients, quotientGenerator, quotientCycle, tailCycle,
          localCycle, pow_two] <;> ring_nf <;>
        simp only [show (2 : Scalar) = 0 from by decide +kernel,
          show (3 : Scalar) = 1 from by decide +kernel,
          show (4 : Scalar) = 0 from by decide +kernel,
          mul_zero, mul_one, add_zero, zero_add]

theorem quotientRepresentation_generated (full : Bool) :
    RepresentationGeneratedBy
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation (quotientLinear full)) 2 := by
  let ρ := LinearSemidirectCoprimeSocleBounds.linearRepresentation (quotientLinear full)
  let v : Fin 2 → ρ.asModule := fun i => ρ.asModuleEquiv.symm (quotientGenerator full i)
  let P : Submodule Scalar[Ternary] ρ.asModule := Submodule.span _ (Set.range v)
  let S : Subrepresentation ρ := Subrepresentation.ofSubmodule' P
  have hv (i : Fin 2) : quotientGenerator full i ∈ S := by
    change v i ∈ P
    exact Submodule.subset_span ⟨i, rfl⟩
  have hc (i : Fin 2) : quotientCycle full (quotientGenerator full i) ∈ S := by
    have hh := S.apply_mem_toSubmodule (Multiplicative.ofAdd 1) (hv i)
    have he : ρ (Multiplicative.ofAdd 1) (quotientGenerator full i) =
        quotientCycle full (quotientGenerator full i) := by
      change (quotientCycle full ^ (1 : ZMod 3).val) _ = _
      rw [ZMod.val_one, pow_one]
    exact he ▸ hh
  have hc₂ (i : Fin 2) : (quotientCycle full ^ 2) (quotientGenerator full i) ∈ S := by
    have hh := S.apply_mem_toSubmodule (Multiplicative.ofAdd 2) (hv i)
    have he : ρ (Multiplicative.ofAdd 2) (quotientGenerator full i) =
        (quotientCycle full ^ 2) (quotientGenerator full i) := rfl
    exact he ▸ hh
  have hS (w : QuotientVector full) : w ∈ S := by
    rw [quotient_orbit_decomposition full w]
    exact S.toSubmodule.add_mem
      (S.toSubmodule.add_mem
        (S.toSubmodule.add_mem
          (S.toSubmodule.add_mem
            (S.toSubmodule.add_mem
              (S.toSubmodule.smul_mem _ (hv 0)) (S.toSubmodule.smul_mem _ (hc 0)))
            (S.toSubmodule.smul_mem _ (hc₂ 0)))
          (S.toSubmodule.smul_mem _ (hv 1)))
        (S.toSubmodule.smul_mem _ (hc 1)))
      (S.toSubmodule.smul_mem _ (hc₂ 1))
  refine ⟨v, top_unique ?_⟩
  intro x hx
  change ρ.asModuleEquiv x ∈ S
  exact hS _

end BinaryFourBlockAugmentation
end SymmetricSubgroupAsymptotics

end
