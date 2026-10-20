import SymmetricSubgroupAsymptotics.Row246OriginalAffineGeneratorCoordinates
import SymmetricSubgroupAsymptotics.KleinParitySignedBinaryTop
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row246OriginalSignedTop
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open KleinParitySignedBinaryTop (Full raw X Y)
abbrev SignedGroup := KleinParitySignedBinaryTop.Group

def signed : row246Interface.top →* Full :=
  TernaryPermutationWreathEmbedding.signMap.comp Row246OriginalTripleFrame.wreathEmbedding

def codes (a : Fin 4) : Full := raw
  (Row246OriginalAffineGeneratorCoordinates.signs a)
  (Row246OriginalTripleFrame.baseCodes a)

theorem signed_generator (a : Fin 4) :
    signed (closureGenerators row246Generators a)=codes a := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact Row246OriginalAffineGeneratorCoordinates.sign_generator a i
  · exact Row246OriginalTripleFrame.top_generator a

private theorem parity_codes : ∀ a : Fin 4, KleinParitySignedBinaryTop.parity (codes a)=1 := by decide +kernel

theorem signed_mem (u : row246Interface.top) : signed u∈SignedGroup := by
  let p := KleinParitySignedBinaryTop.parity.comp signed
  have h : Subgroup.closure (Set.range (closureGenerators row246Generators))≤p.ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a,rfl⟩
    change KleinParitySignedBinaryTop.parity (signed (closureGenerators row246Generators a))=1
    rw [signed_generator]
    exact parity_codes a
  rw [closureGenerators_full row246Generators] at h
  exact h (Subgroup.mem_top u)

def top : row246Interface.top →* SignedGroup := signed.codRestrict SignedGroup signed_mem

theorem top_X : top (closureGenerators row246Generators 2)=X := by
  apply Subtype.ext
  change signed (closureGenerators row246Generators 2)=KleinParitySignedBinaryTop.x
  rw [signed_generator]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    decide +kernel
  · rfl

theorem top_Y : top (closureGenerators row246Generators 3)=Y := by
  apply Subtype.ext
  change signed (closureGenerators row246Generators 3)=KleinParitySignedBinaryTop.y
  rw [signed_generator]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    decide +kernel
  · rfl

@[simp] theorem affine_signed (u : row246Interface.top) :
    (Row246OriginalAffineEmbedding.embedding u).right=signed u := rfl
end SymmetricSubgroupAsymptotics.Row246OriginalSignedTop
