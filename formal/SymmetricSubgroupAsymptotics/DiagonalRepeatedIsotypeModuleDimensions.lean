import SymmetricSubgroupAsymptotics.DiagonalInvariantSubmoduleDimensions
import SymmetricSubgroupAsymptotics.DistinctDiagonalFullCoordinateModule

/-!
# Dimensions of repeated diagonal isotypes with module-valued coordinates

The four-block affine translation coordinates take values in a
one-dimensional local module rather than canonically in the scalar field.
This file scalarizes those coordinates through an arbitrary linear
equivalence and then applies the exact repeated-isotype decomposition.

The last theorem isolates the numerical core of the two-sign argument.  If
there are two character fibres of size two, every coordinate projection is
onto, and the two encoded fibres have equal dimension, then the original
submodule has dimension two or four.  The equality of the two dimensions is
the only place where transitivity of the ambient top is needed later.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace DiagonalInvariantSubmodules

open DiagonalIsotypeProjection

variable {k ι J V : Type*} [Field k] [Fintype ι]
  [AddCommGroup V] [Module k V]

/-- Apply one coordinate linear equivalence at every entry of a function
module. -/
def pointwiseScalarEquiv (e : V ≃ₗ[k] k) :
    (ι → V) ≃ₗ[k] (ι → k) :=
  LinearEquiv.piCongrRight fun _ : ι ↦ e

@[simp] theorem pointwiseScalarEquiv_apply
    (e : V ≃ₗ[k] k) (v : ι → V) (i : ι) :
    pointwiseScalarEquiv (ι := ι) e v i = e (v i) := rfl

/-- A module-valued stable submodule, transported to scalar-valued
coordinates without changing its literal character labels. -/
def scalarizedStable
    (scalar : ι → J → k)
    (K : ModuleStable (V := V) scalar)
    (e : V ≃ₗ[k] k) : Stable scalar := by
  let E := pointwiseScalarEquiv (ι := ι) e
  refine ⟨K.1.map E.toLinearMap, ?_⟩
  intro g y hy
  rcases hy with ⟨x, hx, rfl⟩
  refine ⟨diagonalModuleOperator scalar g x,
    K.2 g x hx, ?_⟩
  funext i
  change e (scalar i g • x i) = scalar i g * e (x i)
  simpa only [map_smul, smul_eq_mul]

/-- Scalarization preserves coordinatewise surjectivity. -/
theorem scalarizedStable_fullCoordinates
    (scalar : ι → J → k)
    (K : ModuleStable (V := V) scalar)
    (e : V ≃ₗ[k] k)
    (hfull : ModuleFullCoordinates K.1) :
    FullCoordinates (scalarizedStable scalar K e).1 := by
  intro i c
  obtain ⟨x, hx⟩ := hfull i (e.symm c)
  let E := pointwiseScalarEquiv (ι := ι) e
  let y : (scalarizedStable scalar K e).1 :=
    ⟨E x.1, ⟨x.1, x.2, rfl⟩⟩
  refine ⟨y, ?_⟩
  change e (x.1 i) = c
  rw [hx, e.apply_symm_apply]

/-- Scalarization preserves the dimension of the original correlated
submodule. -/
theorem scalarizedStable_finrank
    (scalar : ι → J → k)
    (K : ModuleStable (V := V) scalar)
    (e : V ≃ₗ[k] k) :
    Module.finrank k (scalarizedStable scalar K e).1 =
      Module.finrank k K.1 := by
  exact (pointwiseScalarEquiv (ι := ι) e).finrank_map_eq K.1

attribute [local instance] Fintype.ofFinite

/-- Every encoded repeated-isotype component is nonzero when all original
coordinate projections are onto. -/
theorem encode_finrank_pos_of_fullCoordinates
    (scalar : ι → J → k)
    (K : Stable scalar)
    (hfull : FullCoordinates K.1)
    (a : Label scalar) :
    0 < Module.finrank k (encode scalar K a) := by
  have hcomponentFull : FullCoordinates (encode scalar K a) :=
    (fullCoordinates_iff scalar K).mp hfull a
  obtain ⟨i, hi⟩ := a.2
  let j : Coordinate scalar a := ⟨i, hi⟩
  obtain ⟨x, hx⟩ := hcomponentFull j 1
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨x, ?_⟩
  intro hzero
  have hz := congrArg (fun y : encode scalar K a ↦ y.1 j) hzero
  simpa only [hx, Submodule.coe_zero, Pi.zero_apply, one_ne_zero] using hz

/-- Numerical two-sign dimension split after scalarization.  The premise
`component_equidimensional` is designed to be supplied by one ambient-top
element which exchanges the two literal sign classes. -/
theorem moduleStable_finrank_eq_two_or_four_of_two_equal_isotypes
    [Nonempty ι]
    (scalar : ι → J → k)
    (K : ModuleStable (V := V) scalar)
    (e : V ≃ₗ[k] k)
    (hfull : ModuleFullCoordinates K.1)
    (htwo : Nat.card (Label scalar) = 2)
    (hfibre : ∀ a : Label scalar,
      Fintype.card (Coordinate scalar a) = 2)
    (component_equidimensional : ∀ a b : Label scalar,
      Module.finrank k (encode scalar (scalarizedStable scalar K e) a) =
        Module.finrank k (encode scalar (scalarizedStable scalar K e) b)) :
    Module.finrank k K.1 = 2 ∨ Module.finrank k K.1 = 4 := by
  let K' := scalarizedStable scalar K e
  let a₀ : Label scalar := coordinateLabel scalar (Classical.choice inferInstance)
  let d := Module.finrank k (encode scalar K' a₀)
  have hfull' : FullCoordinates K'.1 :=
    scalarizedStable_fullCoordinates scalar K e hfull
  have hdpos : 0 < d :=
    encode_finrank_pos_of_fullCoordinates scalar K' hfull' a₀
  have hdle : d ≤ 2 := by
    calc
      d ≤ Fintype.card (Coordinate scalar a₀) :=
        encode_finrank_le_coordinates scalar K' a₀
      _ = 2 := hfibre a₀
  have hsum : Module.finrank k K'.1 = 2 * d := by
    rw [finrank_eq_sum_encode scalar K']
    simp_rw [component_equidimensional _ a₀]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_eq_nat_card, htwo]
  have hscalar := scalarizedStable_finrank scalar K e
  rw [← hscalar]
  rw [hsum]
  omega

/-- With two equidimensional character components, any stable submodule
has even total dimension.  Unlike the rank-split theorem, this does not
assume that its coordinate projections are onto. -/
theorem moduleStable_finrank_even_of_two_equal_isotypes
    [Nonempty ι]
    (scalar : ι → J → k)
    (K : ModuleStable (V := V) scalar)
    (e : V ≃ₗ[k] k)
    (htwo : Nat.card (Label scalar) = 2)
    (component_equidimensional : ∀ a b : Label scalar,
      Module.finrank k (encode scalar (scalarizedStable scalar K e) a) =
        Module.finrank k (encode scalar (scalarizedStable scalar K e) b)) :
    Even (Module.finrank k K.1) := by
  let K' := scalarizedStable scalar K e
  let a₀ : Label scalar := coordinateLabel scalar (Classical.choice inferInstance)
  let d := Module.finrank k (encode scalar K' a₀)
  have hsum : Module.finrank k K'.1 = 2 * d := by
    rw [finrank_eq_sum_encode scalar K']
    simp_rw [component_equidimensional _ a₀]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_eq_nat_card, htwo]
  have hscalar := scalarizedStable_finrank scalar K e
  refine ⟨d, ?_⟩
  rw [← hscalar, hsum]
  omega

end DiagonalInvariantSubmodules
end SymmetricSubgroupAsymptotics

end
