import SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryPolarCoordinates
import SymmetricSubgroupAsymptotics.QuadraticIsometrySymplecticClassComparison
import SymmetricSubgroupAsymptotics.CFSGSymplecticSmallClassBounds
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedIsometryIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeProjectiveModel
import SymmetricSubgroupAsymptotics.ConjugacyClassSubgroupIndexBound

/-! The SAME actual fixed-space quadratic isometry group is bounded
through its proved binary polar coordinates. The actual relative image
has index at most four in that full group and acts faithfully; its
literal central quotient bounds the original twisted-D model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryIsometryClassBound
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDFixedQuadraticNondegenerate CFSGTwistedDFixedIsometryIndex
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeProjectiveModel
open CFSGTwistedA2FixedField

local instance finiteFixedLinear (n : ℕ) (q : CFSG.PrimePower) :
    Finite (fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q) :=
  Finite.of_injective (fun T : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q =>
    (T : fixedSpace n q → fixedSpace n q)) LinearEquiv.coe_injective

local instance finiteRelative (n : ℕ) (q : CFSG.PrimePower) : Finite (relativeRootGroup n q) :=
  Finite.of_injective (fun g : relativeRootGroup n q =>
    (g.val : CFSGOrthogonalDSerreMatrices.Mat (q.Extension 2) (n+2)))
    (by intro g h he; exact Subtype.ext (Units.ext he))

def relativeIsometryHom (n : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup n q →* fullIsometries n q :=
  (fixedLinearHom n q).codRestrict (fullIsometries n q) (fixedLinearHom_preserves_Q n q)

theorem relativeIsometryHom_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (relativeIsometryHom n q) := by
  intro g h he
  exact fixedLinearHom_injective n q (congrArg Subtype.val he)

theorem relativeIsometryHom_range (n : ℕ) (q : CFSG.PrimePower) :
    (relativeIsometryHom n q).range = (relativeImage n q).subgroupOf (fullIsometries n q) := by
  ext g
  change (∃ x, relativeIsometryHom n q x = g) ↔ ∃ x, fixedLinearHom n q x = g.val
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

private theorem prime_eq_two (q : CFSG.PrimePower) (hq : q.order = 2) : q.prime = 2 :=
  (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
    q.exponent_pos.ne' (by decide : (1 : ℕ) ≠ 0)
    (show q.prime^q.exponent = 2^1 from hq)).1

theorem full_class_card_le (q : CFSG.PrimePower) (hq : q.order = 2) :
    Nat.card (ConjClasses (fullIsometries 2 q)) ≤ 768 := by
  have hp := prime_eq_two q hq
  letI : CharP (fixedField q) 2 := Eq.mp
    (congrArg (fun p : ℕ => CharP (fixedField q) p) hp)
    (inferInstance : CharP (fixedField q) q.prime)
  have hK : Nat.card (fixedField q) = 2 := (fixedField_card q).trans hq
  change Nat.card (ConjClasses
    (CFSGOrthogonalDIndexSingularComponents.isometryGroup (fixedQuadraticForm 2 q))) ≤ 768
  have h := QuadraticIsometrySymplecticClassComparison.class_card_le (fixedField q) hK 3
    (fixedQuadraticForm 2 q) (fixedQuadraticForm_nondegenerate 2 q)
    (CFSGTwistedDBinaryPolarCoordinates.spaceEquiv 2 q hp)
    (CFSGTwistedDBinaryPolarCoordinates.spaceEquiv_preserves 2 q hp)
  exact h.trans (CFSGSymplecticSmallClassBounds.binary_rankFour_add_point (fixedField q) hK)

theorem relative_class_card_le (q : CFSG.PrimePower) (hq : q.order = 2) :
    Nat.card (ConjClasses (relativeRootGroup 2 q)) ≤ 3072 := by
  have h := ConjugacyClassSubgroupIndexBound.class_card_le_injective_index
    (relativeIsometryHom 2 q) (relativeIsometryHom_injective 2 q)
  have hi : (relativeIsometryHom 2 q).range.index ≤ 4 := by
    rw [relativeIsometryHom_range]
    exact relative_index_le_four 2 q
  exact h.trans ((Nat.mul_le_mul hi (full_class_card_le q hq)).trans_eq
    (by decide : 4*768 = 3072))

theorem projective_class_card_le (q : CFSG.PrimePower) (hq : q.order = 2) :
    Nat.card (ConjClasses (relativeRootGroup 2 q ⧸ Subgroup.center (relativeRootGroup 2 q))) ≤
      3072 := by
  let f := QuotientGroup.mk' (Subgroup.center (relativeRootGroup 2 q))
  exact (Nat.card_le_card_of_surjective (ConjClasses.map f)
    (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))).trans
      (relative_class_card_le q hq)

theorem original_class_card_le (q : CFSG.PrimePower) (hq : q.order = 2)
    [IsSimpleGroup (CFSG.Models.TwistedD 4 q)] :
    Nat.card (ConjClasses (CFSG.Models.TwistedD 4 q)) ≤ 3072 := by
  let e := originalRelativeProjectiveEquiv 0 q
  exact (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
    (ConjClasses.map_surjective e.symm.surjective)).trans (projective_class_card_le q hq)

end SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryIsometryClassBound
