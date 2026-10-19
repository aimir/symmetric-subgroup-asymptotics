import SymmetricSubgroupAsymptotics.Row246OriginalSignedTop
import SymmetricSubgroupAsymptotics.Row246Signed32WordCertificate
import SymmetricSubgroupAsymptotics.OrderThirtyTwoBinaryRelativeHeads
import SymmetricSubgroupAsymptotics.PGroupOriginalSocleRelativeHeads

/-! This consumer is prepared ahead of the selected32 word emitter.
Its finite certificate import must be emitted and checked by the primary.
The original signed image is proved onto using literal g2 and g3. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row246SignedTopProfile
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open KleinParitySignedBinaryTop (X Y)
abbrev SignedGroup := KleinParitySignedBinaryTop.Group
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

 theorem top_surjective : Function.Surjective Row246OriginalSignedTop.top := by
  have h : Subgroup.closure (Set.range Row246Signed32WordCertificate.generators)≤
      Row246OriginalSignedTop.top.range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact ⟨closureGenerators row246Generators 2,Row246OriginalSignedTop.top_X⟩
    · exact ⟨closureGenerators row246Generators 3,Row246OriginalSignedTop.top_Y⟩
  rw [Row246Signed32WordCertificate.generators_full] at h
  intro g
  exact h (Subgroup.mem_top g)

 theorem relative_heads (M : Subgroup SignedGroup) [M.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 2 :=
  OrderThirtyTwoBinaryRelativeHeads.relative_head_le_two
    KleinParitySignedBinaryTop.group_card
    (KleinParitySignedBinaryTop.center_card_le_two.trans (by decide))
    (TwoAxisAbelianizationCover.cover X Y)
    Row246Signed32WordCertificate.abelianization_cover_surjective M

 theorem quotient_socles (M : Subgroup SignedGroup) [M.Normal] :
    SocleNormalGeneratorBound (SignedGroup ⧸ M) 2 :=
  PGroupOriginalSocleRelativeHeads.quotientSocle 2
    KleinParitySignedBinaryTop.isPGroup 2
    (fun K => by letI := K.property; exact relative_heads K.val) M
end SymmetricSubgroupAsymptotics.Row246SignedTopProfile
