import SymmetricSubgroupAsymptotics.BinaryFrameEstimates
import SymmetricSubgroupAsymptotics.QuadraticIncidence

/-!
# Retained quadratic incidences for actual subspaces

A linear chart separates the free binary summand from the nonabelian
quadratic factors. Every full subspace is counted with its entire retained
relation space. The ordered-map estimate is converted to a Gaussian count
using the proved ordered-basis fibres.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [Finite W]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
  [∀ i, FiniteDimensional (ZMod 2) (V i)] [∀ i, Finite (V i)]

/-- The literal full-coordinate and simultaneous annihilator conditions on
one actual subspace. All vectors of the retained relation space occur. -/
def FullQuadraticSubspace {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (U : Submodule (ZMod 2) (Fin R → ZMod 2)) : Prop :=
  (∀ i, Function.Surjective (fun u : U ↦ (e u.1).2 i)) ∧
    ∀ b : B, ∀ u : U, ∑ i, b.1 i * q i ((e u.1).2 i) = 0

/-- Ordered injections satisfying the subspace incidence embed in actual
quadratic-relation maps. The injection forgets only injectivity. -/
def quadraticSubspaceMaps {R k : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) :
    {f : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin R → ZMod 2) //
      Function.Injective f ∧ FullQuadraticSubspace e B q f.range} →
      QuadraticRelationMaps (E := Fin k → ZMod 2) (W := W) B q := fun f ↦
  ⟨e.toLinearMap.comp f.1, by
    constructor
    · intro i y
      obtain ⟨u, hu⟩ := f.2.2.1 i y
      obtain ⟨x, hx⟩ := f.1.surjective_rangeRestrict u
      refine ⟨x, ?_⟩
      change (e (f.1 x)).2 i = y
      rw [show f.1 x = u.1 from congrArg Subtype.val hx]
      exact hu
    · intro b x
      exact f.2.2.2 b (f.1.rangeRestrict x)⟩

omit [FiniteDimensional (ZMod 2) W] [Finite W]
  [∀ i, FiniteDimensional (ZMod 2) (V i)] [∀ i, Finite (V i)] in
theorem quadraticSubspaceMaps_injective {R k : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i)) :
    Function.Injective (quadraticSubspaceMaps (k := k) e B q) := by
  intro f g h
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply e.injective
  exact congrArg (fun f : QuadraticRelationMaps (E := Fin k → ZMod 2) (W := W) B q ↦
    f.1 x) h

/-- Each retained relation costs at least two target dimensions and one
bounded realization fibre. This is a bound on actual subspaces, not just
on a catalogue of possible quadratic forms. -/
theorem fullQuadraticSubspace_count_le {R k : ℕ} (hk : k ≤ R)
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (hv : ∀ i, 2 ≤ Module.finrank (ZMod 2) (V i))
    (M : ℕ) (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ M) :
    (Nat.card {U : Submodule (ZMod 2) (Fin R → ZMod 2) //
      Module.finrank (ZMod 2) U = k ∧ FullQuadraticSubspace e B q U} : ℝ) ≤
      eulerProduct⁻¹ * (binaryGaussianCoefficient R k : ℝ) *
        (M : ℝ) ^ Module.finrank (ZMod 2) B /
        (2 : ℝ) ^ (2 * k * Module.finrank (ZMod 2) B) := by
  let l := Module.finrank (ZMod 2) B
  have he : Module.finrank (ZMod 2) W + ∑ i, Module.finrank (ZMod 2) (V i) = R := by
    simpa only [Module.finrank_pi, Fintype.card_fin, Module.finrank_prod,
      Module.finrank_pi_fintype] using e.finrank_eq.symm
  have hl : l ≤ Fintype.card ι := by simpa only [Module.finrank_pi] using B.finrank_le
  have hv' : 2 * Fintype.card ι ≤ ∑ i, Module.finrank (ZMod 2) (V i) := by
    calc
      _ = ∑ _i : ι, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ hv i)
  have h2 : 2 * l ≤ R := by omega
  letI : Finite ((Fin k → ZMod 2) →ₗ[ZMod 2] (W × ∀ i, V i)) :=
    Finite.of_injective (fun f : (Fin k → ZMod 2) →ₗ[ZMod 2] (W × ∀ i, V i) ↦
      (f : (Fin k → ZMod 2) → (W × ∀ i, V i))) DFunLike.coe_injective
  have hcount := (Nat.card_le_card_of_injective (quadraticSubspaceMaps (k := k) e B q)
    (quadraticSubspaceMaps_injective e B q)).trans
    (quadraticRelationMaps_count_le (E := Fin k → ZMod 2) (W := W) B q hq hv M hM)
  have hA : (Nat.card {f : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin R → ZMod 2) //
      Function.Injective f ∧ FullQuadraticSubspace e B q f.range} : ℝ) ≤
      (M : ℝ) ^ l * (2 : ℝ) ^ (k * (R - 2 * l)) := by
    simpa only [Module.finrank_pi, Fintype.card_fin, he, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat] using (show (_ : ℝ) ≤ _ from Nat.cast_le.mpr hcount)
  have h := binary_subspace_incidence_le_gaussian hk (FullQuadraticSubspace e B q) _ hA
  have hexp : R * k = k * (R - 2 * l) + 2 * k * l := by
    have hsub := Nat.sub_add_cancel h2
    nlinarith
  convert h using 1
  rw [hexp, pow_add]
  have hn : (2 : ℝ) ^ (k * (R - 2 * l)) ≠ 0 := by positivity
  field_simp
  ring

end SymmetricSubgroupAsymptotics
