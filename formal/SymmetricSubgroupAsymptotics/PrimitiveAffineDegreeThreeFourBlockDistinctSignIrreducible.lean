import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedTranslationCompatibilityTheorem
import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationSubmoduleCoordinateTransport
import SymmetricSubgroupAsymptotics.TransitiveDiagonalModuleIrreducible

/-!
# Irreducibility in the four-distinct-sign branch

The four-sign theorem makes the literal correlated translation layer the
whole product of its four local one-dimensional modules.  This file uses the
actual block-top transport and the literal diagonal sign kernel to prove
that the quotient action on that layer is irreducible.  No catalogue row or
S3EXC source inequality is used.
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

/-- Coordinate relabelling restricted to the literal correlated translation
submodule. -/
noncomputable def degreeThreeFourBlockTranslationCoordinateMap
    (hs : Nat.card block.Points = 4) :
    TranslationSubmodule block P →ₗ[ZMod P.p]
      (Fin 4 → (chart block P).V) :=
  (coordinateLinearEquiv (k := ZMod P.p)
    (degreeThreeFourBlockIndexEquiv block hs)).toLinearMap.comp
      (TranslationSubmodule block P).subtype

theorem degreeThreeFourBlockTranslationCoordinateMap_injective
    (hs : Nat.card block.Points = 4) :
    Function.Injective
      (degreeThreeFourBlockTranslationCoordinateMap block P hs) :=
  (coordinateLinearEquiv (k := ZMod P.p)
    (degreeThreeFourBlockIndexEquiv block hs)).injective.comp
      (TranslationSubmodule block P).subtype_injective

/-- In the four-sign branch the restricted coordinate map is onto, hence a
linear equivalence with the literal four-coordinate product. -/
noncomputable def degreeThreeFourBlockTranslationCoordinateEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    TranslationSubmodule block P ≃ₗ[ZMod P.p]
      (Fin 4 → (chart block P).V) := by
  let f := degreeThreeFourBlockTranslationCoordinateMap block P hs
  apply LinearEquiv.ofBijective f
  refine ⟨degreeThreeFourBlockTranslationCoordinateMap_injective
    block P hs, ?_⟩
  intro y
  have hy : y ∈ degreeThreeFourBlockReindexedTranslationSubmodule
      block P hs := by
    rw [degreeThreeFourBlock_reindexedTranslationSubmodule_eq_top_of_fourSigns
      block P hr hs hcomponent hbinary hfour]
    exact Submodule.mem_top
  rcases hy with ⟨x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, hxy⟩

/-- The literal pair-kernel inclusion pulled back to the actual quotient
group. -/
noncomputable def degreeThreeFourBlockSignKernelSource
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker →*
      (preE7NonPairAction w U ⧸ E block P) :=
  (degreeThreeFourBlockPairChart block P hr hs hcomponent).sourceEquiv.symm.toMonoidHom.comp
      (degreeThreeFourBlockPairChart
        block P hr hs hcomponent).frame.top.ker.subtype

/-- Every nonzero literal translation coordinate can be moved to every
other coordinate by the actual block top, and stays nonzero under the local
invertible linear factor. -/
theorem degreeThreeFourBlockTranslationCoordinateEquiv_transport
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4)
    (x : TranslationSubmodule block P) (i j : Fin 4)
    (hxi : (degreeThreeFourBlockTranslationCoordinateEquiv
      block P hr hs hcomponent hbinary hfour x) i ≠ 0) :
    ∃ q : preE7NonPairAction w U ⧸ E block P,
      (degreeThreeFourBlockTranslationCoordinateEquiv
        block P hr hs hcomponent hbinary hfour
        ((elementaryChart block P).quotientRepresentation.ρ q x)) j ≠ 0 := by
  let e := degreeThreeFourBlockIndexEquiv block hs
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq block.Top (e.symm i) (e.symm j)
  obtain ⟨a, ha⟩ := block.topMap.rangeRestrict_surjective t
  have hright : (ambientEmbedding block a).right • e.symm i = e.symm j := by
    change block.topMap.rangeRestrict a • e.symm i = e.symm j
    rw [ha]
    exact ht
  refine ⟨QuotientGroup.mk' (E block P) a, ?_⟩
  change (((elementaryChart block P).quotientRepresentation.ρ
    (QuotientGroup.mk' (E block P) a) x).1 (e.symm j)) ≠ 0
  rw [← hright]
  apply translationSubmodule_coordinate_ne_zero_of_transport block P a x
    (e.symm i)
  exact hxi

/-- Four distinct literal sign characters make the actual quotient
representation on the full ternary translation layer irreducible. -/
theorem degreeThreeFourBlock_quotientRepresentation_irreducible
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    Representation.IsIrreducible
      (elementaryChart block P).quotientRepresentation.ρ := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let A := degreeThreeFourBlockSignedTranslationCompatibility
    block P hr hs hcomponent
  let coordinates := degreeThreeFourBlockTranslationCoordinateEquiv
    block P hr hs hcomponent hbinary hfour
  let rho : Representation (ZMod P.p)
      (preE7NonPairAction w U ⧸ E block P)
      (TranslationSubmodule block P) :=
    (elementaryChart block P).quotientRepresentation.ρ
  letI : Fact P.p.Prime := (chart block P).primeFact
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    have hdim' := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at hdim'
    exact hdim'
  letI : Nontrivial (chart block P).V :=
    Module.nontrivial_of_finrank_pos (R := ZMod P.p) (by
      rw [hdim]
      decide)
  letI : Nontrivial (TranslationSubmodule block P) :=
    coordinates.symm.injective.nontrivial
  letI : Nontrivial
      (elementaryChart block P).quotientRepresentation := by
    change Nontrivial (TranslationSubmodule block P)
    infer_instance
  change Representation.IsIrreducible rho
  apply DiagonalInvariantSubmodules.irreducible_of_transitive_diagonal_coordinates
    rho
    coordinates
    (degreeThreeFourBlockSignKernelSource block P hr hs hcomponent)
    (degreeThreeFourBlockTranslationScalar block P hr hs hcomponent)
  · apply degreeThreeFourBlockTranslationScalar_injective block P
    exact degreeThreeFourBlockSignedIsotype_injective_of_count_eq_four
      block P hr hs hcomponent hfour
  · intro k x
    simpa only [coordinates, degreeThreeFourBlockTranslationCoordinateEquiv,
      degreeThreeFourBlockTranslationCoordinateMap,
      degreeThreeFourBlockSignKernelSource, rho, C, A] using
      A.diagonal_action k x
  · exact degreeThreeFourBlockTranslationCoordinateEquiv_transport
      block P hr hs hcomponent hbinary hfour
  · exact hdim

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
