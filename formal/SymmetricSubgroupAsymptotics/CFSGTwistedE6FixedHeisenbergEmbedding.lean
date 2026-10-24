import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedHeisenbergCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveProjection

/-! The descended twenty-one-coordinate Heisenberg group embeds in the
SAME original twisted-E6 model.  Its fixed upper matrix membership and
both faithful maps are actual checked root-product maps; no independent
fixed-source surjectivity or simple-model recognition is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedHeisenbergEmbedding
open CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField
open CFSGExceptionalCartanPositiveDefinite CFSGHeisenbergCoordinateGroup
open CFSGExceptionalHeisenbergProduct CFSGExceptionalHeisenbergPositive
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGTwistedE6HeisenbergCoordinateTwist
open CFSGTwistedE6FixedBilinearPairing CFSGTwistedE6FixedHeisenbergCoordinates
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckFixedPositiveProjection
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def matrixHom (q : CFSG.PrimePower) (delta : Central q) (hdelta : delta.val ≠ 0) :
    Element (fixedField q) 10 →* (Matrix GeckIndex GeckIndex (q.Extension 2))ˣ :=
  (rawHom A hd hs hp ho configuration (q.Extension 2)).comp (coordinateHom q delta hdelta)

theorem matrixHom_injective (q : CFSG.PrimePower) (delta : Central q)
    (hdelta : delta.val ≠ 0) : Function.Injective (matrixHom q delta hdelta) :=
  (rawHom_injective A hd hs hp ho configuration (q.Extension 2)).comp
    (coordinateHom_injective q delta hdelta)

theorem matrixHom_mem_positive (q : CFSG.PrimePower) (delta : Central q)
    (hdelta : delta.val ≠ 0) (g : Element (fixedField q) 10) :
    matrixHom q delta hdelta g ∈ Positive (q.Extension 2) :=
  rawHom_mem_positive A hd hs hp ho configuration (q.Extension 2) (coordinateHom q delta hdelta g)

theorem matrixHom_fixed (q : CFSG.PrimePower) (delta : Central q)
    (hdelta : delta.val ≠ 0) (g : Element (fixedField q) 10) :
    unitTwist (q.Extension 2) (definingFieldAutomorphism q 2) (matrixHom q delta hdelta g) =
      matrixHom q delta hdelta g :=
  (rawHom_fixed_iff (q.Extension 2) (definingFieldAutomorphism q 2)
    (coordinateHom q delta hdelta g)).mpr (coordinateHom_fixed q delta hdelta g)

def fixedPositiveHom (q : CFSG.PrimePower) (delta : Central q) (hdelta : delta.val ≠ 0) :
    Element (fixedField q) 10 →*
      signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false :=
  (matrixHom q delta hdelta).codRestrict
    (signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false)
    (fun g => ⟨matrixHom_mem_positive q delta hdelta g, matrixHom_fixed q delta hdelta g⟩)

theorem fixedPositiveHom_injective (q : CFSG.PrimePower) (delta : Central q)
    (hdelta : delta.val ≠ 0) : Function.Injective (fixedPositiveHom q delta hdelta) := by
  intro g h he
  exact matrixHom_injective q delta hdelta (congrArg Subtype.val he)

def originalHom (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (delta : Central q) (hdelta : delta.val ≠ 0) :
    Element (fixedField q) 10 →* CFSG.Models.TwistedE6 q :=
  (fixedPositiveToOriginal q).comp (fixedPositiveHom q delta hdelta)

theorem originalHom_injective (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (delta : Central q) (hdelta : delta.val ≠ 0) : Function.Injective (originalHom q delta hdelta) :=
  (fixedPositiveToOriginal_injective q).comp (fixedPositiveHom_injective q delta hdelta)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedHeisenbergEmbedding
