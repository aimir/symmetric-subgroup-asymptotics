import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopRelativeKernelOrbitRows
import SymmetricSubgroupAsymptotics.SchurTargetExtension

/-!
# Explicit typewise obligations for the exceptional twelve-pair rows

The stored ordinary-prefix and natural-module maxima cannot be substituted
for the exceptional argument: the pairs `(3,2)` and `(2,3)` exceed the
width-24 slope budget. The five allowed profiles instead require a literal
prefix with binary kernel and bounds on that kernel's canonical omega
socle, with the same simple type retained across its actual layers.

This file is a consumer, not a completed finite catalogue. The prefix
characters, their exact common kernel, the fixed bound, and every nonfixed
Schur multiplicity bound remain explicit construction obligations. No
template below derives them from the two stored scalar maxima.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

local instance finiteDimensionalTypewiseSubmodule
    {k R M : Type} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [FiniteDimensional k M] (S : Submodule R M) : FiniteDimensional k S :=
  FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective

/-- An actual intertwiner permits same-type multiplicities in its kernel
and target to be added before taking the maximum over simple types. This
preserves the correlation discarded by separate scalar Schur capacities. -/
theorem representationSchurCapacity_le_of_sameType_kernel_add
    {k G V W : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (rho : Representation k G V) (sigma : Representation k G W)
    (q : rho.IntertwiningMap sigma) (hq : Function.Surjective q)
    (cap : ℕ)
    (hfixed : Module.finrank k rho.invariants ≤ cap)
    (hsameType : ∀ X : Submodule k[G] rho.asModule,
      [IsSimpleModule k[G] X] →
      ¬ representationSubmoduleFixed rho X →
      schurSocleMultiplicity
          (k := k) (R := k[G]) (A := q.ker.asSubmodule) (X := X) +
        schurSocleMultiplicity
          (k := k) (R := k[G]) (A := sigma.asModule) (X := X) ≤
        cap * Module.finrank (Module.End k[G] X) X) :
    representationSchurCapacity rho ≤ cap := by
  apply Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.representationSchurCapacity_le_of_fixed_nonfixed_multiplicity
    rho cap hfixed
  intro X _hX hnonfixed
  letI : FiniteDimensional k X := FiniteDimensional.of_injective
    (X.subtype.restrictScalars k) X.subtype_injective
  exact (representationSchurMultiplicity_le_kernel_add_target
    (X := X) rho sigma q hq).trans (hsameType X hnonfixed)

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveExceptionalTypewise

/-- Exactly the five existing exceptional profiles; the case records the
kind of prefix, not a new claim about the action census. -/
inductive ProfileKind
  | linearFour
  | binaryFour
  | ordinaryThree
  | twoBinaryThree
  | relativeFour
  deriving DecidableEq

def ProfileKind.profile : ProfileKind → DegreeTwoPairRelativeProfile
  | .linearFour => degreeTwoPairRelativeProfile 0 1 0 4
  | .binaryFour => degreeTwoPairRelativeProfile 1 0 0 4
  | .ordinaryThree => degreeTwoPairRelativeProfile 0 0 1 3
  | .twoBinaryThree => degreeTwoPairRelativeProfile 2 0 0 3
  | .relativeFour => degreeTwoPairRelativeProfile 0 0 0 4

theorem ProfileKind.profile_mem (kind : ProfileKind) :
    kind.profile ∈ degreeTwoTwelvePairExceptionalProfiles := by
  cases kind <;>
    simp [ProfileKind.profile, degreeTwoTwelvePairExceptionalProfiles]

/-- The actual canonical module which the prefix's relative characters
must detect. It is attached to the displayed quotient map. -/
abbrev omegaSocleRepresentation
    {Q B : Type} [Group Q] [Finite Q] [Group B]
    (pi : Q →* B) :=
  (finiteRepresentationSocle
    (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation

/-- The two typewise inequalities needed after a particular prefix has
been chosen. A raw dimension bound on the entire kernel is not required. -/
structure KernelTypewiseBounds
    {Q B : Type} [Group Q] [Finite Q] [Group B]
    (pi : Q →* B) (relative : ℕ) : Prop where
  fixed_le : Module.finrank (ZMod 2)
    (omegaSocleRepresentation pi).invariants ≤ relative
  nonfixed_le : ∀ X : Submodule (ZMod 2)[Q]
      (omegaSocleRepresentation pi).asModule,
    [IsSimpleModule (ZMod 2)[Q] X] →
    ¬ representationSubmoduleFixed (omegaSocleRepresentation pi) X →
    schurSocleMultiplicity
        (k := ZMod 2) (R := (ZMod 2)[Q])
        (A := (omegaSocleRepresentation pi).asModule) (X := X) ≤
      relative * Module.finrank (Module.End (ZMod 2)[Q] X) X

theorem KernelTypewiseBounds.schurCapacity_le
    {Q B : Type} [Group Q] [Finite Q] [Group B]
    {pi : Q →* B} {relative : ℕ} (D : KernelTypewiseBounds pi relative) :
    representationSchurCapacity (omegaSocleRepresentation pi) ≤ relative :=
  representationSchurCapacity_le_of_fixed_nonfixed_multiplicity
    (omegaSocleRepresentation pi) relative D.fixed_le D.nonfixed_le

/-- Concrete data for one original quotient and one allowed profile.
The prefix construction remains visible: in particular, a binary-primary
linear may need higher binary roots, and is not replaced by a sign map. -/
structure QuotientData (Q : Type) [Group Q] [Finite Q]
    (kind : ProfileKind) : Type 1 where
  PrefixTarget : Type
  prefixTargetGroup : Group PrefixTarget
  prefixTargetFinite : Finite PrefixTarget
  quotient : Q →* PrefixTarget
  binary : Fin kind.profile.binaryPrimary → Q →* ℂˣ
  binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range
  linear : Fin kind.profile.linear → Q →* ℂˣ
  ordinary : Fin kind.profile.ordinary → FiniteIrreducibleRepresentation ℂ Q
  kernel_eq : quotient.ker =
    ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
      (⨅ i, (ordinary i).action.ker)
  kernel_twoGroup : IsPGroup 2 quotient.ker
  typewise : KernelTypewiseBounds quotient kind.profile.relative

attribute [instance] QuotientData.prefixTargetGroup QuotientData.prefixTargetFinite

/-- The existing omega-orbit construction supplies the relative irreducible
characters from the two explicit typewise inequalities. -/
def QuotientData.toOrbitInput
    {Q : Type} [Group Q] [Finite Q] {kind : ProfileKind}
    (D : QuotientData Q kind) :
    DegreeTwoPairRelativeKernelOrbitInput Q kind.profile :=
  DegreeTwoPairRelativeKernelOrbitInput.ofSocleSchurCapacity
    D.quotient D.binary D.binary_twoGroup D.linear D.ordinary
    D.kernel_eq D.kernel_twoGroup D.typewise.schurCapacity_le

/-- A selected row's dispatch and raw quotient obligations. The obligations
range over the actual original normal subgroups; the semantic registry does
not discharge them merely by assigning a state index. -/
structure RowData (D : DegreeTwoPairTopFiniteInterface 12)
    (p : PreE7PairActionClass 12)
    (R : DegreeTwoPairTopRealization D p) : Type 1 where
  kindOfState : D.normalRegistry.State → D.ModuleState → ProfileKind
  quotientData : ∀ N : {N : Subgroup (preE7PairAction 12 p) // N.Normal},
    QuotientData (preE7PairAction 12 p ⧸ N.1)
      (kindOfState (R.topNormalState N) (R.moduleState N))

def RowData.toOrbitRow
    {D : DegreeTwoPairTopFiniteInterface 12} {p : PreE7PairActionClass 12}
    {R : DegreeTwoPairTopRealization D p} (F : RowData D p R) :
    DegreeTwoPairTopRelativeKernelOrbitRowData D
      degreeTwoTwelvePairExceptionalProfiles p R where
  stateProfile :=
    { profileOfState := fun i j ↦ (F.kindOfState i j).profile
      allowedProfiles := degreeTwoTwelvePairExceptionalProfiles
      allowed_capacity := degreeTwoTwelvePairExceptionalProfiles_capacity
      profile_mem := fun N ↦
        (F.kindOfState (R.topNormalState N) (R.moduleState N)).profile_mem }
  profiles_eq := rfl
  input N := (F.quotientData N).toOrbitInput

/-- The generic consumer has no numerical premise: its five profile
capacities are already proved by the existing exceptional menu. The
row-specific prefix and typewise certificates are still required in `F`. -/
def RowData.catalogueResolvedRow
    {row : DegreeTwoTwelvePairTopRow}
    {p : PreE7PairActionClass 12}
    {R : DegreeTwoPairTopRealization row.finite p}
    (F : RowData row.finite p R)
    (lit : PreE7CharacterLiterature)
    (hbranch : row.branch = .core ∨ row.branch = .paired) :
    DegreeTwoPairTopResolvedRow row.finite row.expectedProfiles p := by
  have hprofiles : row.expectedProfiles =
      degreeTwoTwelvePairExceptionalProfiles := by
    rcases hbranch with hcore | hpaired
    · rw [row.expectedProfiles_eq, hcore]
    · rw [row.expectedProfiles_eq, hpaired]
  rw [hprofiles]
  exact (F.toOrbitRow.twelveResolvedData lit).toResolvedRow

end DegreeTwoTwelveExceptionalTypewise
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
