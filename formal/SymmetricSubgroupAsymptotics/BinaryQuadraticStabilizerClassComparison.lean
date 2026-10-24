import SymmetricSubgroupAsymptotics.BilinearContragredientDuality
import SymmetricSubgroupAsymptotics.AffineStabilizerClassDomination

/-! Actual quadratic-preserving stabilizers over a field of order two
are bounded by the classes of the polar-preserving group and one actual
nonzero-vector stabilizer. The full fixed-polar refinement space, its
affine action and the dual transitivity are constructed, not supplied as
a class-count or quadratic-type premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryQuadraticStabilizerClassComparison
open BinaryQuadraticRefinementTorsor BinaryQuadraticRefinementAction

variable {G K V : Type*} [Group G] [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [Finite G] [Finite V]

theorem stabilizer_class_card_le (hK : Nat.card K = 2)
    (Q₀ : QuadraticForm K V) (hB : Q₀.polarBilin.Nondegenerate)
    (ρ : G →* (V ≃ₗ[K] V))
    (hρ : ∀ g : G, ∀ x y : V,
      Q₀.polarBilin (ρ g x) (ρ g y) = Q₀.polarBilin x y)
    (v : V) (htrans : ∀ w : V, w ≠ 0 → ∃ g : G, ρ g v = w)
    (Q : Refinement Q₀) :
    letI := refinementAction Q₀ ρ hρ
    letI := BilinearContragredientDuality.naturalAction ρ
    Nat.card (ConjClasses (MulAction.stabilizer G Q)) ≤
      Nat.card (ConjClasses G) + Nat.card (ConjClasses (MulAction.stabilizer G v)) := by
  letI : Module.Finite K V := Module.Finite.of_finite
  letI := refinementAction Q₀ ρ hρ
  letI := dualAction ρ
  letI := BilinearContragredientDuality.naturalAction ρ
  letI : Finite (Refinement Q₀) :=
    Finite.of_injective (fun R : Refinement Q₀ => (R.val : V → K)) (by
      intro R S h
      exact Subtype.ext (QuadraticMap.ext (congrFun h)))
  letI : Finite (Module.Dual K V) :=
    Finite.of_injective (fun f : Module.Dual K V => (f : V → K)) LinearMap.coe_injective
  let B : LinearMap.BilinForm K V := Q₀.polarBilin
  let e := B.toDual hB
  have hdtrans (f : Module.Dual K V) (hf : f ≠ 0) : ∃ g : G, g • e v = f := by
    have hw : e.symm f ≠ 0 := by
      intro h
      apply hf
      have he := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using he
    obtain ⟨g, hg⟩ := htrans (e.symm f) hw
    refine ⟨g, ?_⟩
    have he := BilinearContragredientDuality.toDual_equivariant
      Q₀.polarBilin hB ρ hρ g v
    change e (ρ g v) = g • e v at he
    rw [hg, e.apply_symm_apply] at he
    exact he.symm
  have h := AffineStabilizerClassDomination.stabilizer_class_card_le
    (refinementEquivDual hK Q₀) (translation hK Q₀ ρ hρ)
    (same_linear_part hK Q₀ ρ hρ) (e v) hdtrans Q
  have hs := BilinearContragredientDuality.stabilizer_toDual_eq
    Q₀.polarBilin hB ρ hρ v
  change MulAction.stabilizer G (e v) = MulAction.stabilizer G v at hs
  rw [hs] at h
  exact h

end SymmetricSubgroupAsymptotics.BinaryQuadraticStabilizerClassComparison
