import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerCoupledHeads
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees

/-!
# Finite nested-quotient generator declarations for pair tops

The nonfixed part of a two-frame omega filtration uses only one finite fact
about the literal natural module: every nested invariant quotient either has
cyclic dual or has binary dimension at most two.  Both alternatives imply
the same one-Schur-dimension bound after inflation along any surjective top
map.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Realization-free finite generator certificate for every nested quotient
of the literal natural permutation module. -/
structure DegreeTwoPairTopNestedQuotientGeneratorData
    {t : ℕ} (D : DegreeTwoPairTopFiniteInterface t) : Prop where
  certificate : ∀
    (A B : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)))
    (hAB : A ≤ B),
    RepresentationGeneratedBy
        (nestedQuotientRepresentation A B hAB).dual 1 ∨
      Module.finrank (ZMod 2)
        (nestedQuotientRepresentation A B hAB).asModule ≤ 2

namespace DegreeTwoPairTopNestedQuotientGeneratorData

variable {t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  (Q : DegreeTwoPairTopNestedQuotientGeneratorData D)

/-- The finite generator declaration gives the uniform nonfixed bound after
pullback along any surjective action map. -/
theorem subrepresentationQuotient_comp_nonfixed_le_end_finrank
    {H X : Type*} [Group H]
    (gamma : H →* D.top) (hgamma : Function.Surjective gamma)
    (A B : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)))
    (hAB : A ≤ B)
    [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (sigma : Representation (ZMod 2) H X)
    (S : Submodule (ZMod 2)[H] sigma.asModule)
    [Finite S] [IsSimpleModule (ZMod 2)[H] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := ((nestedQuotientRepresentation A B hAB).comp gamma).asModule)
        (X := S) ≤
      Module.finrank (Module.End (ZMod 2)[H] S) S := by
  letI : FiniteDimensional (ZMod 2) X :=
    Module.Finite.of_finite (ZMod 2) X
  letI : FiniteDimensional (ZMod 2) S :=
    Module.Finite.of_finite (ZMod 2) S
  rcases Q.certificate A B hAB with hgen | hsmall
  · let tau := nestedQuotientRepresentation A B hAB
    have hgenComp : RepresentationGeneratedBy (tau.dual.comp gamma) 1 :=
      RepresentationGeneratedBy.comp_of_surjective
        tau.dual gamma hgamma hgen
    let E := representationDualCompEquiv tau gamma
    have hdual : RepresentationGeneratedBy (tau.comp gamma).dual 1 :=
      representationGeneratedBy_of_surjective
        (tau.dual.comp gamma) (tau.comp gamma).dual
        E.symm.toIntertwiningMap E.symm.surjective hgenComp
    have hschur := schurSocleMultiplicity_le_of_dual_generated
      (tau.comp gamma) 1 hdual (X := S)
    simpa only [tau, one_mul] using hschur
  · have hone : schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[H])
        (A := ((nestedQuotientRepresentation A B hAB).comp gamma).asModule)
        (X := S) ≤ 1 :=
      schurSocleMultiplicity_le_one_of_finrank_le_two_of_nonfixed
        sigma S hnonfixed hsmall
    have hpos : 0 < Module.finrank (Module.End (ZMod 2)[H] S) S := by
      letI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[H] S
      exact Module.finrank_pos
        (R := Module.End (ZMod 2)[H] S) (M := S)
    exact hone.trans hpos

end DegreeTwoPairTopNestedQuotientGeneratorData
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
