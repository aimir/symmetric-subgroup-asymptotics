import SymmetricSubgroupAsymptotics.BinaryBySymmetricThree
import SymmetricSubgroupAsymptotics.Non2SchurScalarOrbit
import SymmetricSubgroupAsymptotics.Non2SchurMixedSocleDimension

/-!
# Binary Schur capacity without an order-three quotient

The only nonfixed binary Schur product degree below three is the scalar
degree-two row. Its literal action has image of order three. Excluding
actual order-three quotients therefore makes every nonfixed row's product
degree at least three. Ambient dimension at most twelve then bounds every
nonfixed Schur density by four. This argument needs neither a classification
of `S₃` modules nor a semisimplicity assumption on the whole target.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {B A : Type} [Group B] [Finite B]
  [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- The scalar degree-two row would exhibit a forbidden literal normal
quotient of order three. -/
theorem three_le_schurSimpleProductDegree_of_noTernaryQuotient
    (hB : NoTernaryQuotient B)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    3 ≤ schurSimpleProductDegree sigma S := by
  have htwo := two_le_schurSimpleProductDegree_of_nonfixed sigma S hnonfixed
  have hne : schurSimpleProductDegree sigma S ≠ 2 := by
    intro heq
    let f := MonoidHom.toHomUnits (schurSimpleActionEndRepresentation sigma S)
    apply hB f.ker
    rw [Subgroup.index_ker]
    exact schurSimpleActionEndRepresentation_range_card_eq_three
      sigma S hnonfixed heq
  omega

/-- One nonfixed simple type uses at most four Schur generator positions
inside a binary target of dimension at most twelve. -/
theorem schurSimpleRatio_le_four_of_noTernaryQuotient
    (hB : NoTernaryQuotient B)
    (sigma : Representation (ZMod 2) B A)
    (hdim : Module.finrank (ZMod 2) A ≤ 12)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    (Module.finrank (ZMod 2) (S →ₗ[(ZMod 2)[B]] sigma.asModule) : ℝ) /
      Module.finrank (ZMod 2) S ≤ 4 := by
  letI : FiniteDimensional (ZMod 2) S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  let q := schurSimpleProductDegree sigma S
  let density : ℝ :=
    (Module.finrank (ZMod 2) (S →ₗ[(ZMod 2)[B]] sigma.asModule) : ℝ) /
      Module.finrank (ZMod 2) S
  have hq : (3 : ℝ) ≤ q := by
    exact_mod_cast three_le_schurSimpleProductDegree_of_noTernaryQuotient
      hB sigma S hnonfixed
  have hnonneg : 0 ≤ density := schurSimpleRatio_nonneg sigma S
  have hoccupied : Module.finrank (ZMod 2) S *
      schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[B])
        (A := sigma.asModule) (X := S) ≤ 12 :=
    (finrank_mul_schurSocleMultiplicity_le
      (k := ZMod 2) (R := (ZMod 2)[B]) (A := sigma.asModule) (X := S)).trans
      (by rw [sigma.asModuleEquiv.finrank_eq]; exact hdim)
  have hproduct : (q : ℝ) * density ≤ 12 := by
    change (schurSimpleProductDegree sigma S : ℝ) *
      ((Module.finrank (ZMod 2) (S →ₗ[(ZMod 2)[B]] sigma.asModule) : ℝ) /
        Module.finrank (ZMod 2) S) ≤ 12
    rw [schurSimpleProductDegree_mul_ratio sigma S 0]
    simp only [schurMixedSocleDimension, zero_add, Nat.cast_zero, sub_zero]
    exact_mod_cast hoccupied
  change density ≤ 4
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) hnonneg]

/-- The fixed and nonfixed rows share four generator positions. The
fixed-rank premise refers to the literal invariant subspace. -/
theorem representationSchurCapacity_le_four_of_noTernaryQuotient
    (hB : NoTernaryQuotient B)
    (sigma : Representation (ZMod 2) B A)
    (hdim : Module.finrank (ZMod 2) A ≤ 12)
    (hfixed : Module.finrank (ZMod 2) sigma.invariants ≤ 4) :
    representationSchurCapacity sigma ≤ 4 := by
  apply (representationSchurCapacity_le_max_fixed_nontrivial sigma 4 ?_).trans
    (max_le (by exact_mod_cast hfixed) le_rfl)
  intro S hS hnonfixed
  letI : IsSimpleModule (ZMod 2)[B] S := hS
  exact schurSimpleRatio_le_four_of_noTernaryQuotient hB sigma hdim S hnonfixed

end SymmetricSubgroupAsymptotics

end
