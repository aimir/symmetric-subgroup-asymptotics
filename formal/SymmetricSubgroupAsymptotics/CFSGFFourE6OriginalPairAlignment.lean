import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGOppositeSylowOfAlignment

/-! Inner adjustment of an arbitrary automorphism of the SAME original
simple F4 model preserves the actual positive and negative images. Both
the disjoint Sylow pair and the alignment are conclusions of literal
matrix/source constructions; no automorphism lift is an assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPairAlignment
open CFSGFFourE6OriginalOppositeAlignment CFSGFFourE6OriginalProjection
open CFSGFFourE6ProjectiveOrder CFSGFFourE6PositiveActionInjective
open CFSGFFourE6FixedPositiveProjection CFSGFFourE6SignedFixedInclusion
open CFSGFFourOriginalGoodSylow CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGTwistedE6GeckRelativeRootGenerated CFSG.Models.Chevalley
local instance imageFinite (K : Type) [Field K] [Finite K] : Finite (imageGroup K) :=
  Finite.of_surjective (foldedToImage K) (foldedToImage_surjective K)
local instance originalFinite (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : Finite (Projective CartanMatrix.F₄ K) :=
  original_finite K

def originalOppositeSylow (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : Sylow p (Projective CartanMatrix.F₄ K) :=
  (imageNegativeSylow K p).mapSurjective (f:=imageToOriginal K) (imageToOriginal_surjective K)

theorem original_opposite_sylows_disjoint (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K))⊓
      (originalOppositeSylow K p : Subgroup (Projective CartanMatrix.F₄ K))=⊥ := by
  change ((imagePositiveSylow K p : Subgroup (imageGroup K)).map (imageToOriginal K))⊓
    ((imageNegativeSylow K p : Subgroup (imageGroup K)).map (imageToOriginal K))=⊥
  exact CFSGCentralKernelPElements.disjoint_map (imageToOriginal K) (imagePositiveSylow K p)
    (positiveToOriginal_injective K p) (le_of_eq (imageToOriginal_kernel K))
    (imagePositiveSylow K p : Subgroup (imageGroup K)) (imageNegativeSylow K p : Subgroup (imageGroup K))
    (imagePositiveSylow K p).isPGroup' (imageNegativeSylow K p).isPGroup' (imageSylows_disjoint K p)

theorem original_negative_is_sylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    ∃S : Sylow p (Projective CartanMatrix.F₄ K),
      (S : Subgroup (Projective CartanMatrix.F₄ K))=originalNegative K ∧
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K))⊓
        (S : Subgroup (Projective CartanMatrix.F₄ K))=⊥ :=
  CFSGOppositeSylowOfAlignment.exists_negative_sylow (originalPositiveSylow K p)
    (originalOppositeSylow K p) (originalNegative K) (original_opposite_sylows_disjoint K p)
    (original_opposite_conjugate_by_positive K p)

theorem original_exists_inner_fix_pair (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K)) :
    ∃g : Projective CartanMatrix.F₄ K,
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map
        (MulAut.conj g*f).toMonoidHom=(originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) ∧
      (originalNegative K).map (MulAut.conj g*f).toMonoidHom=originalNegative K :=
  CFSGOppositeSylowOfAlignment.exists_inner_fix_pair (originalPositiveSylow K p)
    (originalOppositeSylow K p) (originalNegative K) (original_opposite_sylows_disjoint K p)
    (original_opposite_conjugate_by_positive K p) f

theorem signedFixedToOriginal_range (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (neg : Bool) :
    (signedFixedToOriginal K neg).range=
      ((signedFixed K (RingEquiv.refl K) neg).subgroupOf
        (canonicalElementaryGroup realizationData K)).map (foldedToOriginal K) := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨signedFixedToFolded K neg u,u.property,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨⟨u.val,hu⟩,rfl⟩

theorem signedFixedToOriginal_positive (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    signedFixedToOriginal K false=fixedPositiveToOriginal K p := rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPairAlignment
