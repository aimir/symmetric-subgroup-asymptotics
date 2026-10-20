import SymmetricSubgroupAsymptotics.BinaryFourFullBlockActions
import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
import SymmetricSubgroupAsymptotics.PermutationalWreathFunctionCoinducedEquiv

/-! Canonical A4 induced-plane chart, on the actual four block points.
Its local representation extends by the ternary quotient; the full eight
coordinates are exactly the existing fullChart, not a new finite frame. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryFourCanonicalInducedChart

open BinaryFourBlockAugmentation BinaryFourFullBlockCoordinates

private def kleinBlocks : Klein →* Equiv.Perm (Fin 4) where
  toFun p := blockU ^ (p.toAdd 0).val * blockV ^ (p.toAdd 1).val
  map_one' := by apply Equiv.ext; intro i; revert i; decide +kernel
  map_mul' := by intro p q; apply Equiv.ext; intro i; revert p q i; decide +kernel

private theorem blockC_cube : blockC ^ 3 = 1 := by
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

private def ternaryBlocks : Ternary →* Equiv.Perm (Fin 4) :=
  powersHom 3 blockC blockC_cube

private theorem blockCompatibility (z : Ternary) :
    kleinBlocks.comp (kleinCyclicAction z).toMonoidHom =
      (MulAut.conj (ternaryBlocks z)).toMonoidHom.comp kleinBlocks := by
  apply MonoidHom.ext
  intro p
  apply Equiv.ext
  intro i
  revert z p i
  decide +kernel

def blocks : Complement →* Equiv.Perm (Fin 4) :=
  SemidirectProduct.lift kleinBlocks ternaryBlocks blockCompatibility

instance canonicalBlockAction : MulAction Complement (Fin 4) := MulAction.compHom (Fin 4) blocks

instance canonicalBlockTransitive : MulAction.IsPretransitive Complement (Fin 4) := ⟨by
  intro i j
  have hc : ∀ i j : Fin 4, ∃ p : Klein,
      blocks (SemidirectProduct.inl p) i = j := by decide +kernel
  obtain ⟨p, hp⟩ := hc i j
  exact ⟨SemidirectProduct.inl p, hp⟩⟩

def localLinear : Ternary →* (Local ≃ₗ[Scalar] Local) :=
  powersHom 3 localCycle localCycle_cube

abbrev LocalLinearGroup := Local ≃ₗ[Scalar] Local

def localPlaneRepresentation : Representation Scalar LocalLinearGroup Local :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation (MonoidHom.id LocalLinearGroup)

def wreath : Complement →* PermutationalWreathProduct LocalLinearGroup Complement (Fin 4) where
  toFun r := ⟨fun _ => localLinear r.right, r⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      exact localLinear.map_one
    · rfl
  map_mul' r s := by
    apply PermutationalWreathProduct.ext
    · funext i
      exact localLinear.map_mul r.right s.right
    · rfl

def fullRepresentation : Representation Scalar Complement BinaryFourBlockAugmentation.Module :=
  PermutationalWreathProduct.FunctionCoinduced.fullRepresentation wreath localPlaneRepresentation

def fullCoordinatesRepresentation : Representation Scalar Complement FullCoordinates :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation fullComplementLinear

def fullCoordinatesEquiv : fullCoordinatesRepresentation.Equiv fullRepresentation where
  toLinearEquiv := fullChart
  isIntertwining' := by
    intro r
    apply (Pi.basisFun Scalar (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rcases r with ⟨p, z⟩
    revert p z i
    decide +kernel

def stabilizer : Subgroup Complement :=
  PermutationalWreathProduct.FunctionCoinduced.stabilizer wreath (0 : Fin 4)

def localRepresentation : Representation Scalar stabilizer Local :=
  PermutationalWreathProduct.FunctionCoinduced.localRepresentation
    wreath localPlaneRepresentation 0

def fullCoinducedChart : fullCoordinatesRepresentation.Equiv
    (Representation.coind stabilizer.subtype localRepresentation) :=
  fullCoordinatesEquiv.trans
    (PermutationalWreathProduct.FunctionCoinduced.fullCoinducedEquiv
      wreath localPlaneRepresentation 0 (fun r => ⟨r, rfl⟩))

end SymmetricSubgroupAsymptotics.BinaryFourCanonicalInducedChart

end
