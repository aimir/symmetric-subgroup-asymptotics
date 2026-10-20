import SymmetricSubgroupAsymptotics.BinaryFourCanonicalInducedChart
import SymmetricSubgroupAsymptotics.BinaryFourSymmetricBlockPermutation

/-! The canonical full S4 induced-plane chart. Both the block reflection
and the local reflection are the retained ones used by symmetricLinear. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricInducedChart

open BinaryFourBlockAugmentation BinaryFourFullBlockCoordinates
open BinaryFourSymmetricBlockActions

private theorem blockReflection_square : (Equiv.swap (2 : Fin 4) 3) ^ 2 = 1 := by
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

private def binaryBlocks : Binary →* Equiv.Perm (Fin 4) :=
  powersHom 2 (Equiv.swap 2 3) blockReflection_square

private theorem blocksCompatibility (b : Binary) :
    BinaryFourCanonicalInducedChart.blocks.comp (complementBinaryAction b).toMonoidHom =
      (MulAut.conj (binaryBlocks b)).toMonoidHom.comp BinaryFourCanonicalInducedChart.blocks := by
  apply MonoidHom.ext
  intro r
  apply Equiv.ext
  intro i
  rcases r with ⟨p, z⟩
  revert b p z i
  decide +kernel

def blocks : SymmetricComplement →* Equiv.Perm (Fin 4) :=
  SemidirectProduct.lift BinaryFourCanonicalInducedChart.blocks binaryBlocks blocksCompatibility

instance canonicalBlockAction : MulAction SymmetricComplement (Fin 4) :=
  MulAction.compHom (Fin 4) blocks

instance canonicalBlockTransitive : MulAction.IsPretransitive SymmetricComplement (Fin 4) := ⟨by
  intro i j
  have hc : ∀ i j : Fin 4, ∃ p : Klein,
      blocks (SemidirectProduct.inl (SemidirectProduct.inl p)) i = j := by decide +kernel
  obtain ⟨p, hp⟩ := hc i j
  exact ⟨SemidirectProduct.inl (SemidirectProduct.inl p), hp⟩⟩

private def ternaryLocal : Complement →* BinaryFourCanonicalInducedChart.LocalLinearGroup :=
  BinaryFourCanonicalInducedChart.localLinear.comp SemidirectProduct.rightHom

private theorem localReflection_square : localReflection ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

private def binaryLocal : Binary →* BinaryFourCanonicalInducedChart.LocalLinearGroup :=
  powersHom 2 localReflection localReflection_square

private theorem localCompatibility (b : Binary) :
    ternaryLocal.comp (complementBinaryAction b).toMonoidHom =
      (MulAut.conj (binaryLocal b)).toMonoidHom.comp ternaryLocal := by
  apply MonoidHom.ext
  intro r
  apply LinearEquiv.ext
  intro x
  rcases r with ⟨p, z⟩
  revert b p z x
  decide +kernel

def localLinear : SymmetricComplement →* BinaryFourCanonicalInducedChart.LocalLinearGroup :=
  SemidirectProduct.lift ternaryLocal binaryLocal localCompatibility

def wreath : SymmetricComplement →*
    PermutationalWreathProduct BinaryFourCanonicalInducedChart.LocalLinearGroup
      SymmetricComplement (Fin 4) where
  toFun r := ⟨fun _ => localLinear r, r⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      exact localLinear.map_one
    · rfl
  map_mul' r s := by
    apply PermutationalWreathProduct.ext
    · funext i
      exact localLinear.map_mul r s
    · rfl

def fullRepresentation : Representation Scalar SymmetricComplement
    BinaryFourBlockAugmentation.Module :=
  PermutationalWreathProduct.FunctionCoinduced.fullRepresentation wreath
    BinaryFourCanonicalInducedChart.localPlaneRepresentation

def fullCoordinatesRepresentation : Representation Scalar SymmetricComplement FullCoordinates :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation symmetricLinear

def fullCoordinatesEquiv : fullCoordinatesRepresentation.Equiv fullRepresentation where
  toLinearEquiv := fullChart
  isIntertwining' := by
    intro r
    apply (Pi.basisFun Scalar (Fin 8)).ext
    intro i
    rw [Pi.basisFun_apply]
    rcases r with ⟨⟨p, z⟩, b⟩
    revert p z b i
    decide +kernel

def stabilizer : Subgroup SymmetricComplement :=
  PermutationalWreathProduct.FunctionCoinduced.stabilizer wreath (0 : Fin 4)

def localRepresentation : Representation Scalar stabilizer Local :=
  PermutationalWreathProduct.FunctionCoinduced.localRepresentation
    wreath BinaryFourCanonicalInducedChart.localPlaneRepresentation 0

def fullCoinducedChart : fullCoordinatesRepresentation.Equiv
    (Representation.coind stabilizer.subtype localRepresentation) :=
  fullCoordinatesEquiv.trans
    (PermutationalWreathProduct.FunctionCoinduced.fullCoinducedEquiv
      wreath BinaryFourCanonicalInducedChart.localPlaneRepresentation 0 (fun r => ⟨r, rfl⟩))

end SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricInducedChart

end
