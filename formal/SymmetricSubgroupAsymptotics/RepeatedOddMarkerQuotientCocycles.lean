import SymmetricSubgroupAsymptotics.RepeatedOddMarkerImage
import SymmetricSubgroupAsymptotics.TernaryDiagonalQuotientCocycles

/-!
# Install the exact cocycle count on an original repeated-marker state

The source is the literal sign/exterior image of H and the quotient is by
the literal reconstructed ternary kernel of H. Binaryity, invariance and
nontrivial signs are all obtained from the original action. No independence
of marker coordinates or assumed cocycle cardinality is required.

This is the cocycle side of the exact fibre formula; identifying the whole
fixed-image/fixed-kernel subgroup fibre remains a separate correspondence.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerQuotientCocycles

open groupCohomology RepeatedOddMarkerKernel RepeatedOddMarkerModule RepeatedOddMarkerImage

variable {ι D : Type} [Fintype ι] [Group D]
    (H : Subgroup ((ι → OddMarkerGroup) × D))

def quotientRep : Rep (ZMod 3) (image H) :=
  TernaryDiagonalQuotientCocycles.quotientRep (RepeatedOddMarkerImage.signCharacter H)
    (kernelSubmodule H) (RepeatedOddMarkerImage.diagonal_mem H)

private theorem character_ne_one (i : ι) (hfull : H.map (coordinate i)=⊤) :
    RepeatedOddMarkerImage.signCharacter H i ≠ 1 := by
  obtain ⟨b,hb⟩ := RepeatedOddMarkerImage.signCharacter_nontrivial H i hfull
  intro h
  apply hb
  exact DFunLike.congr_fun h b

/-- The actual differential is an equivalence on this actual quotient. -/
def principalEquiv (hD : IsPGroup 2 D)
    (hfull : ∀ i, H.map (coordinate i)=⊤) :
    quotientRep H ≃ₗ[ZMod 3] cocycles₁ (quotientRep H) :=
  TernaryDiagonalQuotientCocycles.principalEquiv
    (RepeatedOddMarkerImage.signCharacter H) (kernelSubmodule H)
    (RepeatedOddMarkerImage.diagonal_mem H) (image_isPGroup hD H)
    (fun i => character_ne_one H i (hfull i))

theorem cocycles_card (hD : IsPGroup 2 D)
    (hfull : ∀ i, H.map (coordinate i)=⊤) :
    Nat.card (cocycles₁ (quotientRep H)) =
      Nat.card ((ι → ZMod 3) ⧸ kernelSubmodule H) :=
  (Nat.card_congr (principalEquiv H hD hfull).toEquiv).symm

theorem cocycles_card_pow (hD : IsPGroup 2 D)
    (hfull : ∀ i, H.map (coordinate i)=⊤) :
    Nat.card (cocycles₁ (quotientRep H)) =
      3 ^ (Fintype.card ι - Module.finrank (ZMod 3) (kernelSubmodule H)) :=
  TernaryDiagonalQuotientCocycles.cocycles_card_pow
    (RepeatedOddMarkerImage.signCharacter H) (kernelSubmodule H)
    (RepeatedOddMarkerImage.diagonal_mem H) (image_isPGroup hD H)
    (fun i => character_ne_one H i (hfull i))

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerQuotientCocycles

end
