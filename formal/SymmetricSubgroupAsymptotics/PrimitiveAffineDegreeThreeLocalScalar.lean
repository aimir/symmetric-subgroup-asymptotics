import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryExceptionalLocal

/-!
# The literal scalar of a degree-three affine complement

For a local affine component of degree three, the translation module is
one-dimensional.  The exact compressed local complement therefore acts by
a unique scalar.  This file names that scalar and proves that it still
separates elements of the literal local quotient.  No identification of the
local module with a chosen copy of `F₃` is made.

This is the local algebra needed to compare the actual four signed pair
characters with the diagonal action on the correlated translation
submodule.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Canonical scalar-field transport forced by local degree three. -/
noncomputable def degreeThreeScalarFieldEquiv
    (hr : Nat.card block.Fibre = 3) : ZMod P.p ≃+* ZMod 3 :=
  ZMod.ringEquivCongr (degreeThree_translation_prime_dim block P hr).1

/-- The unique scalar through which one element of the actual compressed
local complement acts on the one-dimensional translation module. -/
noncomputable def degreeThreeLocalScalar
    (hr : Nat.card block.Fibre = 3)
    (q : LocalQuotient block P) : ZMod P.p := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  exact Classical.choose
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
      (degreeThree_translation_prime_dim block P hr).2
      ((binaryAffineLocalLinearRepresentation block P).ρ q))

/-- The transported local representation is literally multiplication by
the selected scalar. -/
theorem degreeThreeLocalScalar_action
    (hr : Nat.card block.Fibre = 3)
    (q : LocalQuotient block P) (v : (chart block P).V) :
    (binaryAffineLocalLinearRepresentation block P).ρ q v =
      degreeThreeLocalScalar block P hr q • v := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  have hscalar := (Classical.choose_spec
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
      (degreeThree_translation_prime_dim block P hr).2
      ((binaryAffineLocalLinearRepresentation block P).ρ q))).1
  simpa using LinearMap.congr_fun hscalar v

/-- The scalar attached to the identity local complement is one. -/
@[simp] theorem degreeThreeLocalScalar_one
    (hr : Nat.card block.Fibre = 3) :
    degreeThreeLocalScalar block P hr 1 = 1 := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  have hunique := (Classical.choose_spec
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
      (degreeThree_translation_prime_dim block P hr).2
      ((binaryAffineLocalLinearRepresentation block P).ρ (1 :
        LocalQuotient block P)))).2
  symm
  apply hunique
  rw [map_one]
  ext v
  change v = (1 : ZMod P.p) • v
  simp only [one_smul]

/-- Faithfulness of the literal local complement survives the scalar
compression. -/
theorem degreeThreeLocalScalar_injective
    (hr : Nat.card block.Fibre = 3) :
    Function.Injective (degreeThreeLocalScalar block P hr) := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  intro q r hqr
  apply binaryAffineLocalLinearRepresentation_injective block P
  ext v
  rw [degreeThreeLocalScalar_action block P hr,
    degreeThreeLocalScalar_action block P hr, hqr]

@[simp] theorem degreeThreeLocalScalar_eq_iff
    (hr : Nat.card block.Fibre = 3)
    (q r : LocalQuotient block P) :
    degreeThreeLocalScalar block P hr q =
        degreeThreeLocalScalar block P hr r ↔
      q = r :=
  (degreeThreeLocalScalar_injective block P hr).eq_iff

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
