import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarScalarTransport
import SymmetricSubgroupAsymptotics.CFSGFiniteScalarConjugation

/-! The actual base-field automorphism of an ORIGINAL unitary star
stabilizer. The ring laws and bijectivity follow from conjugation of
the proved scalar centroid and finiteness of the actual Frobenius-fixed
field; no field semilinearity is supplied to the construction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField

def unitaryStarScalarRing (q : CFSG.PrimePower) : fixedField q →+*
    AddMonoid.End (CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) where
  toFun a := CFSGHermitianTwoByTwoRankOne.fixedScaleHom (definingFieldAutomorphism q 2) a.val a.property
  map_zero' := by
    apply AddMonoidHom.ext
    intro A
    apply Subtype.ext
    ext i j
    change 0 * A.val i j = 0
    exact zero_mul _
  map_one' := by
    apply AddMonoidHom.ext
    intro A
    exact CFSGHermitianTwoByTwoRankOne.fixedScaleHom_one (definingFieldAutomorphism q 2) A
  map_add' a b := by
    apply AddMonoidHom.ext
    intro A
    apply Subtype.ext
    ext i j
    change (a.val + b.val) * A.val i j = a.val * A.val i j + b.val * A.val i j
    ring
  map_mul' a b := by
    apply AddMonoidHom.ext
    intro A
    exact (CFSGHermitianTwoByTwoRankOne.fixedScaleHom_mul
      (definingFieldAutomorphism q 2) a.val b.val a.property b.property A).symm

theorem unitaryStarScalarRing_injective (q : CFSG.PrimePower) :
    Function.Injective (unitaryStarScalarRing q) := by
  intro a b he
  have h := congrArg (fun f : AddMonoid.End
    (CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) =>
      f (CFSGHermitianTwoByTwoRankOne.ray (definingFieldAutomorphism q 2)
        (fun z => extension_two_pow_twice q z) 0)) he
  have h00 := congrArg (fun A : CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2) =>
    A.val 0 0) h
  apply Subtype.ext
  change a.val * 1 = b.val * 1 at h00
  simpa only [mul_one] using h00

theorem unitaryStarScalarRing_conjugate (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s) :
    ∀ a : fixedField q, ∃ b : fixedField q,
      CFSGFiniteScalarConjugation.additiveConjugation (unitaryStarCoefficientAut q s t ht htc f hinc)
        (unitaryStarScalarRing q a) = unitaryStarScalarRing q b := by
  intro a
  obtain ⟨b, hb, he⟩ := unitaryStarCoefficientAut_transports_fixed_scalars q s t ht htc f hinc a.val a.property
  refine ⟨⟨b, hb⟩, ?_⟩
  apply AddMonoidHom.ext
  intro A
  change unitaryStarCoefficientAut q s t ht htc f hinc
    (CFSGHermitianTwoByTwoRankOne.fixedScaleHom (definingFieldAutomorphism q 2) a.val a.property
      ((unitaryStarCoefficientAut q s t ht htc f hinc).symm A)) = _
  simpa only [AddEquiv.apply_symm_apply] using he ((unitaryStarCoefficientAut q s t ht htc f hinc).symm A)

def unitaryStarFixedFieldAut (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s) :
    fixedField q ≃+* fixedField q :=
  CFSGFiniteScalarConjugation.descendedEquiv (unitaryStarScalarRing q) (unitaryStarScalarRing_injective q)
    (CFSGFiniteScalarConjugation.additiveConjugation (unitaryStarCoefficientAut q s t ht htc f hinc))
    (unitaryStarScalarRing_conjugate q s t ht htc f hinc)

theorem unitaryStarFixedFieldAut_intertwines (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s)
    (a : fixedField q)
    (A : CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) :
    unitaryStarCoefficientAut q s t ht htc f hinc (unitaryStarScalarRing q a A) =
      unitaryStarScalarRing q (unitaryStarFixedFieldAut q s t ht htc f hinc a)
        (unitaryStarCoefficientAut q s t ht htc f hinc A) := by
  have hh := CFSGFiniteScalarConjugation.descendedEquiv_spec
    (unitaryStarScalarRing q) (unitaryStarScalarRing_injective q)
    (CFSGFiniteScalarConjugation.additiveConjugation (unitaryStarCoefficientAut q s t ht htc f hinc))
    (unitaryStarScalarRing_conjugate q s t ht htc f hinc) a
  have he := congrArg (fun F : AddMonoid.End
    (CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) =>
      F (unitaryStarCoefficientAut q s t ht htc f hinc A)) hh
  change unitaryStarCoefficientAut q s t ht htc f hinc
    (unitaryStarScalarRing q a ((unitaryStarCoefficientAut q s t ht htc f hinc).symm
      (unitaryStarCoefficientAut q s t ht htc f hinc A))) = _ at he
  simpa only [AddEquiv.symm_apply_apply] using he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
