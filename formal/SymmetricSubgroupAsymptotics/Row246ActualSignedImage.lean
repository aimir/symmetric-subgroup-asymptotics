import SymmetricSubgroupAsymptotics.Row246SignedTopProfile
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row246ActualSignedImage
open Row246OriginalAffineEmbedding
open KleinParitySignedBinaryTop (E)
abbrev SignedGroup := KleinParitySignedBinaryTop.Group
open LinearSemidirectSubgroupKernelChart
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev action := TernarySignedPermutationSubgroupSocles.linearAction E
abbrev actualImage := Image action image

theorem image_eq : actualImage=SignedGroup := by
  apply le_antisymm
  · rintro _ ⟨k,rfl⟩
    obtain ⟨u,hu⟩ := k.property
    change k.val.right∈SignedGroup
    rw [← hu]
    exact Row246OriginalSignedTop.signed_mem u
  · intro g hg
    obtain ⟨u,hu⟩ := Row246SignedTopProfile.top_surjective ⟨g,hg⟩
    refine ⟨embedding.rangeRestrict u,?_⟩
    exact congrArg Subtype.val hu

 theorem transitive : ∀ x y : Fin 4,∃ g : actualImage,
    TernarySignedPermutationSubgroupSocles.blockPermutation E g.val x=y := by
  have h : ∀ x y : Fin 4,∃ (v : KleinParitySignedBinaryTop.Vector)
      (b : FourBlockKleinSignBase.Base),
      KleinParitySignedBinaryTop.parity (KleinParitySignedBinaryTop.raw v b)=1 ∧
      FourBlockKleinSignBase.blocks b x=y := by decide +kernel
  intro x y
  obtain ⟨v,b,hp,hb⟩ := h x y
  refine ⟨⟨KleinParitySignedBinaryTop.raw v b,?_⟩,?_⟩
  · rw [image_eq]
    exact hp
  · exact hb

 theorem isPGroup : IsPGroup 2 actualImage := by
  rw [image_eq]
  exact KleinParitySignedBinaryTop.isPGroup

 theorem relative_heads (L : Subgroup actualImage) [L.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 L) ≤ 2 := by
  have aux : ∀ (S : Subgroup KleinParitySignedBinaryTop.Full), S=SignedGroup →
      ∀ (M : Subgroup S) (hM : M.Normal),
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 2 := by
    intro S h M hM
    subst S
    letI := hM
    exact Row246SignedTopProfile.relative_heads M
  exact aux actualImage image_eq L inferInstance
end SymmetricSubgroupAsymptotics.Row246ActualSignedImage
