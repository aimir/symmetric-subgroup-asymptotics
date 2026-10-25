import SymmetricSubgroupAsymptotics.CFSGFFourBinaryFoldedRadicalNormalizer
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryRadicalCentralLayers

/-! Actual normalizer coordinates for the binary radical inside the
folded F4 source. The radical and central chart retain their faithful
literal embeddings; the final projection is the already proved original
F4 projection, rather than a newly recognized group model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryActualNormalizerCoordinates
open CFSGFFourBinaryFoldedRadicalNormalizer CFSGFFourBinaryFixedRadicalEmbedding
open CFSGFFourBinaryRadicalCentralLayers CFSGFFourE6OriginalProjection
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
local instance fFourActualNormalizerRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
variable (K : Type) [Field K] [Finite K] [CharP K 2]

abbrev Normalizer := Subgroup.normalizer
  ((foldedHom K).range : Set (canonicalElementaryGroup realizationData K))

def normalRadical : Subgroup (Normalizer K) := (foldedHom K).range.subgroupOf (Normalizer K)

instance normalRadical_normal : (normalRadical K).Normal :=
  inferInstanceAs ((foldedHom K).range.subgroupOf (Normalizer K)).Normal

def radicalHom : Radical K →* Normalizer K :=
  (foldedHom K).codRestrict (Normalizer K)
    (fun r => (foldedHom K).range.le_normalizer ⟨r,rfl⟩)

theorem radicalHom_injective : Function.Injective (radicalHom K) := by
  intro r s h
  exact foldedHom_injective K (congrArg Subtype.val h)

private def radicalIntoNormal : Radical K →* normalRadical K :=
  (radicalHom K).codRestrict (normalRadical K) (fun r => ⟨r,rfl⟩)

def normalRadicalEquiv : Radical K ≃* normalRadical K :=
  MulEquiv.ofBijective (radicalIntoNormal K) ⟨by
    intro r s h
    apply radicalHom_injective K
    exact congrArg Subtype.val h,by
    intro n
    obtain ⟨r,hr⟩ := n.property
    refine ⟨r,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hr⟩

def centralHom : CentralCoordinates K →* Normalizer K :=
  (radicalHom K).comp (centralCoordinates K)

theorem centralHom_injective : Function.Injective (centralHom K) :=
  (radicalHom_injective K).comp (centralCoordinates_injective K)

theorem centralHom_mem_normalRadical (z : CentralCoordinates K) :
    centralHom K z ∈ normalRadical K := ⟨centralCoordinates K z,rfl⟩

theorem centralHom_commutes_normalRadical (n : normalRadical K) (z : CentralCoordinates K) :
    (n : Normalizer K) * centralHom K z = centralHom K z * n := by
  obtain ⟨r,hr⟩ := (normalRadicalEquiv K).surjective n
  rw [←hr]
  exact ((centralCoordinates_commute K z r).symm.map (radicalHom K)).eq

variable [IsSimpleGroup (CFSG.Models.Chevalley.Projective CartanMatrix.F₄ K)]

def originalProjection : Normalizer K →* CFSG.Models.Chevalley.Projective CartanMatrix.F₄ K :=
  (foldedToOriginal K).comp (Normalizer K).subtype

theorem originalProjection_radical (r : Radical K) :
    originalProjection K (radicalHom K r) = originalHom K r := rfl

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryActualNormalizerCoordinates
