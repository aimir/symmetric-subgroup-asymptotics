import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionPairKernelFaithful

/-!
# Faithfulness of the literal pair kernel on the full translation layer

In the rank-two bottom branch the full ternary translation layer itself is
the two-dimensional section whose linear image must be recognized.  The
literal pair kernel acts faithfully on that layer.  Indeed, every nontrivial
pair-kernel element changes one sign isotype, while coordinate surjectivity
supplies a vector with nonzero coordinate in that isotype.  The literal
diagonal-action identity then rules out trivial action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open DiagonalInvariantSubmodules

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance : Fact P.p.Prime := (chart block P).primeFact

/-- Restriction of the full quotient representation to the literal
`C₂²` pair kernel. -/
def degreeThreeFourBlockTwoSignBottomPairKernelRepresentation
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    Representation (ZMod P.p) C.frame.top.ker
      (TranslationSubmodule block P) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  exact (elementaryChart block P).quotientRepresentation.ρ.comp
    (C.sourceEquiv.symm.toMonoidHom.comp C.frame.top.ker.subtype)

@[simp] theorem degreeThreeFourBlockTwoSignBottomPairKernelRepresentation_apply
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker) :
    degreeThreeFourBlockTwoSignBottomPairKernelRepresentation
        block P hr hs hcomponent k =
      (elementaryChart block P).quotientRepresentation.ρ
        ((degreeThreeFourBlockPairChart
          block P hr hs hcomponent).sourceEquiv.symm k.1) := rfl

/-- The literal pair kernel acts faithfully on the full correlated
translation layer. -/
theorem degreeThreeFourBlockTwoSignBottomPairKernelRepresentation_injective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    Function.Injective
      (degreeThreeFourBlockTwoSignBottomPairKernelRepresentation
        block P hr hs hcomponent) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let scalar := degreeThreeFourBlockTranslationScalar
    block P hr hs hcomponent
  let A := degreeThreeFourBlockSignedTranslationCompatibility
    block P hr hs hcomponent
  let K := DegreeThreeFourBlockSignedTranslationCompatibility.stable
    (block := block) (P := P) A
  let e := degreeThreeFourBlockLocalScalarEquiv block P hr
  let KA := scalarizedStable scalar K e
  have hfull : FullCoordinates KA.1 :=
    scalarizedStable_fullCoordinates scalar K e
      (DegreeThreeFourBlockSignedTranslationCompatibility.fullCoordinates
        (block := block) (P := P) A hbinary)
  have hker : ∀ k : C.frame.top.ker,
      degreeThreeFourBlockTwoSignBottomPairKernelRepresentation
          block P hr hs hcomponent k = 1 → k = 1 := by
    intro k hk
    by_contra hk1
    obtain ⟨a, ha⟩ := degreeThreeFourBlockTwoSign_exists_isotype_ne_one
      block P hr hs hcomponent k hk1
    let i : Fin 4 := Classical.choose a.2
    have hi : scalar i = a.1 := Classical.choose_spec a.2
    obtain ⟨y, hy⟩ := hfull i 1
    rcases y.2 with ⟨x₀, hx₀, hxy⟩
    let x : degreeThreeFourBlockReindexedTranslationSubmodule block P hs :=
      ⟨x₀, hx₀⟩
    let v : TranslationSubmodule block P :=
      (degreeThreeFourBlockReindexedTranslationEquiv block P hs).symm x
    have haction :
        (elementaryChart block P).quotientRepresentation.ρ
            (C.sourceEquiv.symm k.1) v = v := by
      have happ := congrArg
        (fun f : Module.End (ZMod P.p) (TranslationSubmodule block P) =>
          f v) hk
      simpa only [
        degreeThreeFourBlockTwoSignBottomPairKernelRepresentation_apply,
        Module.End.one_apply, C, v] using happ
    have hv : coordinateLinearEquiv (k := ZMod P.p)
        (degreeThreeFourBlockIndexEquiv block hs) v.1 = x.1 := by
      exact congrArg Subtype.val
        ((degreeThreeFourBlockReindexedTranslationEquiv
          block P hs).apply_symm_apply x)
    have hdiag := A.diagonal_action k v
    rw [haction, hv] at hdiag
    have hcoordinate := congrArg
      (fun z : Fin 4 → (chart block P).V => e (z i)) hdiag.symm
    have hxyi := congrFun hxy i
    have hyi : y.1 i = 1 := hy
    have haki : a.1 k = 1 := by
      change scalar i k * e (x.1 i) = e (x.1 i) at hcoordinate
      rw [hxyi, hyi, hi, mul_one] at hcoordinate
      exact hcoordinate
    exact ha haki
  intro x y hxy
  have hxy1 :
      degreeThreeFourBlockTwoSignBottomPairKernelRepresentation
          block P hr hs hcomponent (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  exact inv_mul_eq_one.mp (hker (x⁻¹ * y) hxy1)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
