import SymmetricSubgroupAsymptotics.RepresentationNestedQuotientFixedExtension
import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees

/-!
# Finite certificates after removing fixed upper layers

A cyclic dual or a quotient of binary dimension at most two bounds each
nonfixed Schur row by one Schur dimension. The same bound survives adding
any number of pointwise fixed upper layers. This inductive certificate
records those layers instead of incorrectly requiring the whole dual to be
cyclic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (rho : Representation (ZMod 2) G V)

/-- A finite derivation of the one-Schur-dimension nonfixed bound. -/
inductive BinaryNestedQuotientNonfixedCertificate :
    (A B : Subrepresentation rho) → (A ≤ B) → Prop
  | cyclic (A B) (hAB : A ≤ B)
      (h : RepresentationGeneratedBy (nestedQuotientRepresentation A B hAB).dual 1) :
      BinaryNestedQuotientNonfixedCertificate A B hAB
  | small (A B) (hAB : A ≤ B)
      (h : Module.finrank (ZMod 2) (nestedQuotientRepresentation A B hAB).asModule ≤ 2) :
      BinaryNestedQuotientNonfixedCertificate A B hAB
  | fixedExtension (A C B) (hAC : A ≤ C) (hCB : C ≤ B)
      (hdisplacements : ∀ g v, v ∈ B → rho g v - v ∈ C)
      (previous : BinaryNestedQuotientNonfixedCertificate A C hAC) :
      BinaryNestedQuotientNonfixedCertificate A B (hAC.trans hCB)

namespace BinaryNestedQuotientNonfixedCertificate

variable {rho}

theorem of_generated_or_small (A B : Subrepresentation rho) (hAB : A ≤ B)
    (h : RepresentationGeneratedBy (nestedQuotientRepresentation A B hAB).dual 1 ∨
      Module.finrank (ZMod 2) (nestedQuotientRepresentation A B hAB).asModule ≤ 2) :
    BinaryNestedQuotientNonfixedCertificate rho A B hAB :=
  h.elim (cyclic A B hAB) (small A B hAB)

/-- Every certified nested quotient has the required nonfixed bound after
any surjective pullback of the group action. -/
theorem comp_nonfixed_le_end_finrank
    [Finite V] [FiniteDimensional (ZMod 2) V]
    {A B : Subrepresentation rho} {hAB : A ≤ B}
    (C : BinaryNestedQuotientNonfixedCertificate rho A B hAB)
    {H X : Type} [Group H]
    (gamma : H →* G) (hgamma : Function.Surjective gamma)
    [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (sigma : Representation (ZMod 2) H X)
    (S : Submodule (ZMod 2)[H] sigma.asModule)
    [Finite S] [IsSimpleModule (ZMod 2)[H] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[H])
        (A := (inflatedRepresentation gamma (nestedQuotientRepresentation A B hAB)).asModule)
        (X := S) ≤ Module.finrank (Module.End (ZMod 2)[H] S) S := by
  letI : FiniteDimensional (ZMod 2) X := Module.Finite.of_finite
  letI : FiniteDimensional (ZMod 2) S := Module.Finite.of_finite
  induction C with
  | cyclic B hAB hgen =>
      let tau := nestedQuotientRepresentation A B hAB
      have hgenComp : RepresentationGeneratedBy (inflatedRepresentation gamma tau.dual) 1 :=
        RepresentationGeneratedBy.comp_of_surjective tau.dual gamma hgamma hgen
      let E := representationDualCompEquiv tau gamma
      have hdual : RepresentationGeneratedBy (inflatedRepresentation gamma tau).dual 1 :=
        representationGeneratedBy_of_surjective
          (inflatedRepresentation gamma tau.dual) (inflatedRepresentation gamma tau).dual
          E.symm.toIntertwiningMap E.symm.surjective hgenComp
      simpa only [tau, one_mul] using
        schurSocleMultiplicity_le_of_dual_generated
          (inflatedRepresentation gamma tau) 1 hdual (X := S)
  | small B hAB hsmall =>
      have hone : schurSocleMultiplicity
          (k := ZMod 2) (R := (ZMod 2)[H])
          (A := (inflatedRepresentation gamma (nestedQuotientRepresentation A B hAB)).asModule)
          (X := S) ≤ 1 :=
        schurSocleMultiplicity_le_one_of_finrank_le_two_of_nonfixed
          sigma S hnonfixed hsmall
      have hpos : 0 < Module.finrank (Module.End (ZMod 2)[H] S) S := by
        letI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[H] S
        have hdim := Module.finrank_pos (R := ZMod 2) (M := S)
        have htower := schur_simple_finrank_tower
          (k := ZMod 2) (R := (ZMod 2)[H]) (X := S)
        exact Nat.pos_of_mul_pos_left (htower ▸ hdim)
      exact hone.trans hpos
  | fixedExtension C B hAC hCB hd _ ih =>
      exact (nestedQuotient_comp_nonfixed_le_of_displacements gamma A C B hAC hCB
        hd sigma S hnonfixed).trans ih

end BinaryNestedQuotientNonfixedCertificate
end SymmetricSubgroupAsymptotics

end
