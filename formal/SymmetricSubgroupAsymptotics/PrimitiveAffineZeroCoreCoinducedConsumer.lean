import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameFullFrameInduced
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTopStabilizerEpi
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFiniteFrameSource
import SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-!
Return a bound on the actual permutation top and its actual stabilizer
frame to the original degree-four affine profile. The translation module
is its correlated original submodule, included in the full frame and then
in the coinduced frame. Every original normal axis is retained by the
existing finite-frame consumer. This module does not supply a catalogue
or assert either of the numerical inputs independently of its caller.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance : Fact P.p.Prime := (chart block P).primeFact

/-- The exact correlated translation module in the original induced fibre. -/
def translationSubmoduleToCoinduced (i : block.Points) :
    (show Representation (ZMod P.p) (DegreeFourComplementQuotient block P)
        (TranslationSubmodule block P) from
      (elementaryChart block P).quotientRepresentation.ρ).IntertwiningMap
      (Representation.coind (fullFrameInducedStabilizer block P i).subtype
        (fullFrameInducedLocalRepresentation block P i)) :=
  (PermutationalWreathProduct.FunctionCoinduced.toCoinduced
    (quotientEmbedding block P) (binaryAffineLocalLinearRepresentation block P).ρ i).comp
      (translationSubmoduleFullFrameEmbedding block P)

theorem translationSubmoduleToCoinduced_injective (i : block.Points) :
    Function.Injective (translationSubmoduleToCoinduced block P i) := by
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  exact (PermutationalWreathProduct.FunctionCoinduced.toCoinduced_injective
    (quotientEmbedding block P) (binaryAffineLocalLinearRepresentation block P).ρ i
    (binaryAffineQuotientTopMap_surjective block P)).comp
      (translationSubmoduleFullFrameEmbedding_injective block P)

/-- The original local representation displayed directly on the faithful
permutation top's stabilizer. -/
abbrev zeroCoreTopLocalRepresentation
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) (i : block.Points) :
    Representation (ZMod P.p) (MulAction.stabilizer block.Top i) (chart block P).V :=
  (binaryAffineLocalLinearRepresentation block P).ρ.comp
    (degreeFourZeroCoreTopStabilizerLocalMap block P hr hD i)

/-- Exact local compatibility, on the unchanged chart vector space. -/
def zeroCoreInducedLocalEquiv
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) (i : block.Points) :
    Representation.Equiv (fullFrameInducedLocalRepresentation block P i)
      ((zeroCoreTopLocalRepresentation block P hr hD i).comp
        (degreeFourZeroCoreTopStabilizerEquiv block P hr hD i).toMonoidHom) :=
  Representation.Equiv.mk (LinearEquiv.refl (ZMod P.p) (chart block P).V) (by
    intro h
    apply LinearMap.ext
    intro v
    change (binaryAffineLocalLinearRepresentation block P).ρ
        (binaryAffineStabilizerComponent block P i h) v =
      (binaryAffineLocalLinearRepresentation block P).ρ
        (binaryAffineStabilizerComponent block P i
          ((degreeFourZeroCoreTopStabilizerEquiv block P hr hD i).symm
            ((degreeFourZeroCoreTopStabilizerEquiv block P hr hD i) h))) v
    rw [MulEquiv.symm_apply_apply])

/-- Uniform coinduced heads on the literal top control the actual
correlated translation module, before any normal quotient is chosen. -/
theorem translationModuleHead_of_top_coinduced
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) (i : block.Points) (cap : ℕ)
    (hhead : ∀ B : Subrepresentation
      (Representation.coind (MulAction.stabilizer block.Top i).subtype
        (zeroCoreTopLocalRepresentation block P hr hD i)),
      Module.finrank (ZMod P.p)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod P.p) block.Top (ZMod P.p))) ≤ cap) :
    DegreeFourZeroCoreTranslationModuleHeadBound block P cap := by
  classical
  let Q := DegreeFourComplementQuotient block P
  let H := fullFrameInducedStabilizer block P i
  let rho := fullFrameInducedLocalRepresentation block P i
  letI : Fintype Q := Fintype.ofFinite Q
  letI : FiniteDimensional (ZMod P.p) (Representation.coindV H.subtype rho) :=
    FiniteDimensional.of_injective (Representation.coindV H.subtype rho).subtype
      (Representation.coindV H.subtype rho).subtype_injective
  have hcoind : ∀ B : Subrepresentation (Representation.coind H.subtype rho),
      Module.finrank (ZMod P.p)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod P.p) Q (ZMod P.p))) ≤ cap :=
    CoinducedGroupLocalTransport.uniform_head_le H (MulAction.stabilizer block.Top i)
      (degreeFourZeroCoreTopEquiv block P hr hD)
      (degreeFourZeroCoreTopStabilizerEquiv block P hr hD i)
      (fun _ => rfl) rho (zeroCoreTopLocalRepresentation block P hr hD i)
      (zeroCoreInducedLocalEquiv block P hr hD i) cap hhead
  letI : FiniteDimensional (ZMod (elementaryChart block P).p)
      (elementaryChart block P).quotientRepresentation := by
    change FiniteDimensional (ZMod P.p) (TranslationSubmodule block P)
    exact FiniteDimensional.of_injective
      (translationSubmoduleToCoinduced block P i).toLinearMap
      (translationSubmoduleToCoinduced_injective block P i)
  intro B
  letI : FiniteDimensional (ZMod (elementaryChart block P).p) B.toSubmodule :=
    FiniteDimensional.of_injective B.toSubmodule.subtype B.toSubmodule.subtype_injective
  have h := uniformSubrepresentationHeadBound_of_injective
    (show Representation (ZMod P.p) Q (TranslationSubmodule block P) from
      (elementaryChart block P).quotientRepresentation.ρ)
    (Representation.coind H.subtype rho)
    (translationSubmoduleToCoinduced block P i)
    (translationSubmoduleToCoinduced_injective block P i) cap hcoind B
  exact (representationHead_finrank_eq_coinvariants B.toRepresentation).symm.trans_le h

/-- Shared original-profile consumer for both structural and finite rows.
Its two inputs are on the actual faithful top, not on an unrelated overgroup. -/
def DegreeFourZeroCoreFiniteFrameBounds.ofTopCoinduced
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) (i : block.Points)
    (topSlots moduleSlots slots : ℕ) (hsum : topSlots + moduleSlots ≤ slots)
    (htop : ∀ (N : Subgroup block.Top) [N.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ topSlots)
    (hhead : ∀ B : Subrepresentation
      (Representation.coind (MulAction.stabilizer block.Top i).subtype
        (zeroCoreTopLocalRepresentation block P hr hD i)),
      Module.finrank (ZMod P.p)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod P.p) block.Top (ZMod P.p))) ≤ moduleSlots) :
    DegreeFourZeroCoreFiniteFrameBounds block P slots where
  topSlots := topSlots
  moduleSlots := moduleSlots
  slot_sum_le := hsum
  topRelativeBinaryRank := by
    intro N
    letI : N.1.Normal := N.2
    let e := degreeFourZeroCoreTopEquiv block P hr hD
    let M := N.1.map e.toMonoidHom
    letI : M.Normal := Subgroup.Normal.map inferInstance _ e.surjective
    rw [← (relativeCharacterAmbientCongr 2 e N.1 M rfl).finrank_eq]
    exact htop M
  translationModuleHead :=
    translationModuleHead_of_top_coinduced block P hr hD i moduleSlots hhead

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
