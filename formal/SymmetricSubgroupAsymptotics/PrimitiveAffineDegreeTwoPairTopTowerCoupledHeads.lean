import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopTowerQuotient
import SymmetricSubgroupAsymptotics.BinaryCoupledHeadCertificate

/-!
# Coupled relative heads for a two-frame pair tower

The paired-eight rows use a single finite table on the literal degree-eight
top.  The table bounds three heads simultaneously: the image in the inner
pair kernel, the pair-sum image of the outer kernel, and the remaining
pair-constant quotient after the product/commutator denominator is removed.

This file attaches that table to the three semantic axes constructed from
an arbitrary original normal subgroup.  Thus a generated coupled registry
is enough to prove the exact inequality used in the paired-eight argument;
no enumeration of normal subgroups of the subsequent degree-thirty-two
pair lift is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- A complete coupled-head table on the literal bottom top of a two-frame
pair tower.  Its state indexing is deliberately independent of the module
index stored in `DegreeTwoPairTopFiniteInterface`: selected generated rows
may use a smaller explicit invariant-subspace registry while semantic
completeness still covers every actual axis. -/
structure DegreeTwoPairTopTowerCoupledHeadData
    {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
    {p : PreE7PairActionClass s}
    (R : DegreeTwoPairTopTowerRealization D p)
    (cap : ℕ) : Type 1 where
  Generator : Type
  State : Type
  generators : Generator → D.top
  state : State → Subrepresentation
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
  registry : BinaryInvariantCompleteCoupledHeadRegistry
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    generators state cap

namespace DegreeTwoPairTopTowerCoupledHeadData

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {p : PreE7PairActionClass s}
  {R : DegreeTwoPairTopTowerRealization D p}
  {cap : ℕ}
  (C : DegreeTwoPairTopTowerCoupledHeadData R cap)

/-- The literal three-layer demand attached to one original normal axis.
The final term retains the product span in its denominator, rather than
replacing it by an unrelated subspace. -/
def omegaHeadDemand
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) : ℕ :=
  Module.finrank (ZMod 2)
      (R.innerOmegaNaturalAxis N).toRepresentation.Coinvariants +
    Module.finrank (ZMod 2)
      (R.outerOmegaPairSumAxis N).toRepresentation.Coinvariants +
    Module.finrank (ZMod 2)
      ((R.outerOmegaConstantAxis N).toSubmodule ⫽
        binaryCoupledDenominator
          (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
          C.generators (R.outerOmegaConstantAxis N)
          (binaryCoordinateProductSpan
            (R.innerOmegaNaturalAxis N).toSubmodule
            (R.outerOmegaPairSumAxis N).toSubmodule)
          (R.omegaAxes_productSpan_le N))

/-- The third coupled row as an actual quotient representation of the
literal top, with the product commutator and all intrinsic displacements
divided out. -/
abbrev omegaIntrinsicCoupledQuotientRepresentation
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :=
  binaryIntrinsicCoupledQuotientRepresentation
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    (R.innerOmegaNaturalAxis N)
    (R.outerOmegaPairSumAxis N)
    (R.outerOmegaConstantAxis N)
    (R.omegaAxes_productSpan_le N)

/-- The actual third coupled row is fixed pointwise by the literal top. -/
@[simp] theorem omegaIntrinsicCoupledQuotientRepresentation_apply
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (g : D.top)
    (z : (C.omegaIntrinsicCoupledQuotientRepresentation N).asModule) :
    C.omegaIntrinsicCoupledQuotientRepresentation N g z = z :=
  binaryIntrinsicCoupledQuotientRepresentation_apply
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    (R.innerOmegaNaturalAxis N)
    (R.outerOmegaPairSumAxis N)
    (R.outerOmegaConstantAxis N)
    (R.omegaAxes_productSpan_le N) g z

theorem omegaIntrinsicCoupledQuotientRepresentation_invariants_eq_top
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (C.omegaIntrinsicCoupledQuotientRepresentation N).invariants = ⊤ := by
  apply top_unique
  intro z _ g
  exact C.omegaIntrinsicCoupledQuotientRepresentation_apply N g z

/-- Thus the quotient dimension in the coupled demand is literally the
dimension of the fixed row of its residual representation. -/
theorem omegaIntrinsicCoupledQuotientRepresentation_invariants_finrank_eq
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (C.omegaIntrinsicCoupledQuotientRepresentation N).invariants =
      Module.finrank (ZMod 2)
        (C.omegaIntrinsicCoupledQuotientRepresentation N).asModule := by
  rw [C.omegaIntrinsicCoupledQuotientRepresentation_invariants_eq_top N,
    finrank_top]

/-- The same residual row with the literal stored-generator denominator
appearing in `omegaHeadDemand`. -/
abbrev omegaCoupledQuotientRepresentation
    (hgen : Subgroup.closure (Set.range C.generators) = ⊤)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :=
  binaryCoupledQuotientRepresentation
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    C.generators hgen
    (R.innerOmegaNaturalAxis N)
    (R.outerOmegaPairSumAxis N)
    (R.outerOmegaConstantAxis N)
    (R.omegaAxes_productSpan_le N)

@[simp] theorem omegaCoupledQuotientRepresentation_apply
    (hgen : Subgroup.closure (Set.range C.generators) = ⊤)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal})
    (g : D.top)
    (z : (C.omegaCoupledQuotientRepresentation hgen N).asModule) :
    C.omegaCoupledQuotientRepresentation hgen N g z = z :=
  binaryCoupledQuotientRepresentation_apply
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    C.generators hgen
    (R.innerOmegaNaturalAxis N)
    (R.outerOmegaPairSumAxis N)
    (R.outerOmegaConstantAxis N)
    (R.omegaAxes_productSpan_le N) g z

theorem omegaCoupledQuotientRepresentation_invariants_eq_top
    (hgen : Subgroup.closure (Set.range C.generators) = ⊤)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (C.omegaCoupledQuotientRepresentation hgen N).invariants = ⊤ := by
  apply top_unique
  intro z _ g
  exact C.omegaCoupledQuotientRepresentation_apply hgen N g z

theorem omegaCoupledQuotientRepresentation_invariants_finrank_eq
    (hgen : Subgroup.closure (Set.range C.generators) = ⊤)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (C.omegaCoupledQuotientRepresentation hgen N).invariants =
      Module.finrank (ZMod 2)
        ((R.outerOmegaConstantAxis N).toSubmodule ⫽
          binaryCoupledDenominator
            (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
            C.generators (R.outerOmegaConstantAxis N)
            (binaryCoordinateProductSpan
              (R.innerOmegaNaturalAxis N).toSubmodule
              (R.outerOmegaPairSumAxis N).toSubmodule)
            (R.omegaAxes_productSpan_le N)) := by
  rw [C.omegaCoupledQuotientRepresentation_invariants_eq_top hgen N,
    finrank_top]

/-- Representation-level form of the complete finite-table demand: two
intrinsic invariant-form heads and one actual fixed quotient row. -/
theorem omegaHeadDemand_eq_head_add_head_add_fixed
    (hgen : Subgroup.closure (Set.range C.generators) = ⊤)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    C.omegaHeadDemand N =
      Module.finrank (ZMod 2)
          ((R.innerOmegaNaturalAxis N).toRepresentation.IntertwiningMap
            (Representation.trivial (ZMod 2) D.top (ZMod 2))) +
        Module.finrank (ZMod 2)
          ((R.outerOmegaPairSumAxis N).toRepresentation.IntertwiningMap
            (Representation.trivial (ZMod 2) D.top (ZMod 2))) +
        Module.finrank (ZMod 2)
          (C.omegaCoupledQuotientRepresentation hgen N).invariants := by
  unfold omegaHeadDemand
  rw [representationHead_finrank_eq_coinvariants,
    representationHead_finrank_eq_coinvariants,
    C.omegaCoupledQuotientRepresentation_invariants_finrank_eq hgen N]

/-- When the stored tuple generates the literal top, the third coupled
term uses the full intrinsic displacement subspace of `L`.  Thus the
catalogue demand is exactly `d(K) + d(W) + dim L/(KW + [L,S])`. -/
theorem omegaHeadDemand_eq_intrinsic
    (hgen : Subgroup.closure (Set.range C.generators) = ⊤)
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    C.omegaHeadDemand N =
      Module.finrank (ZMod 2)
          (R.innerOmegaNaturalAxis N).toRepresentation.Coinvariants +
        Module.finrank (ZMod 2)
          (R.outerOmegaPairSumAxis N).toRepresentation.Coinvariants +
        Module.finrank (ZMod 2)
          ((R.outerOmegaConstantAxis N).toSubmodule ⫽
            ((binaryCoordinateProductSpan
                (R.innerOmegaNaturalAxis N).toSubmodule
                (R.outerOmegaPairSumAxis N).toSubmodule).comap
                  (R.outerOmegaConstantAxis N).toSubmodule.subtype ⊔
              Representation.Coinvariants.ker
                (R.outerOmegaConstantAxis N).toRepresentation)) := by
  unfold omegaHeadDemand
  rw [binaryCoupledDenominator_eq_sup_coinvariantsKer
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    C.generators (R.outerOmegaConstantAxis N) hgen]

/-- The complete generated table applies to the semantic axes selected by
every original normal subgroup.  This is the formal version of the
coupled inequality

`d(K) + d(W) + dim L / (KW + [L,S]) ≤ cap`.
-/
theorem omegaHeadDemand_le
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    C.omegaHeadDemand N ≤ cap :=
  C.registry.finrank_add_finrank_add_quotient_le
    (R.innerOmegaNaturalAxis N)
    (R.outerOmegaPairSumAxis N)
    (R.outerOmegaConstantAxis N)
    (R.omegaAxes_productSpan_le N)

/-- Expanded form for downstream filtration proofs which need to rewrite
the three terms separately. -/
theorem omegaHeads_add_quotient_le
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Module.finrank (ZMod 2)
        (R.innerOmegaNaturalAxis N).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2)
        (R.outerOmegaPairSumAxis N).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2)
        ((R.outerOmegaConstantAxis N).toSubmodule ⫽
          binaryCoupledDenominator
            (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
            C.generators (R.outerOmegaConstantAxis N)
            (binaryCoordinateProductSpan
              (R.innerOmegaNaturalAxis N).toSubmodule
              (R.outerOmegaPairSumAxis N).toSubmodule)
            (R.omegaAxes_productSpan_le N)) ≤ cap :=
  C.omegaHeadDemand_le N

end DegreeTwoPairTopTowerCoupledHeadData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
