import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylowCenterFamily

/-! Arbitrary automorphisms of the ORIGINAL simple projective Serre model
preserve the conjugate family of its actual projected dominant-root
subgroup. The proof uses the displayed literal Sylow and its FULL centre;
it neither lifts automorphisms nor assumes faithfulness of the source Lie
algebra. Exceptional sign/word premises are installed separately. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamily
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinatePositiveQuotientInjectivity CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalPositiveSylow
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem original_projective_finite [Finite K]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Finite (Projective (cartan b₀ s₀) K) :=
  Finite.of_surjective (originalProjection A hd hs hp ho K i)
    (originalProjection_surjective A hd hs hp ho K i)

def originalRootLine [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (θ : Roots A) : Subgroup (Projective (cartan b₀ s₀) K) :=
  ((rootSubgroup A hd hs hp ho K θ).subgroupOf (PositiveGroup A hd hs hp ho K)).map
    ((originalProjection A hd hs hp ho K i).comp (positiveInclusion A hd hs hp ho K))

def originalConjugateRootLine [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (θ : Roots A) (g : Projective (cartan b₀ s₀) K) :
    Subgroup (Projective (cartan b₀ s₀) K) :=
  (originalRootLine A hd hs hp ho K i θ).map (MulAut.conj g).toMonoidHom

theorem automorphism_maps_originalConjugateRootLine [Finite K] [Nontrivial (Fin r)]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))
    (f : MulAut (Projective (cartan b₀ s₀) K)) (g : Projective (cartan b₀ s₀) K) :
    ∃h : Projective (cartan b₀ s₀) K,
      (originalConjugateRootLine A hd hs hp ho K i θ g).map f.toMonoidHom=
        originalConjugateRootLine A hd hs hp ho K i θ h := by
  letI : Finite (Projective (cartan b₀ s₀) K) := original_projective_finite A hd hs hp ho K i
  let P := originalPositiveSylow A hd hs hp ho K ε hε hA hidentity p i
  have hP : (P : Subgroup (Projective (cartan b₀ s₀) K))=originalPositive A hd hs hp ho K i :=
    originalPositiveSylow_coe A hd hs hp ho K ε hε hA hidentity p i
  have hcenter : CFSGOrthogonalDIndexSylowCenterFamily.centerImage (P : Subgroup (Projective (cartan b₀ s₀) K)) =
      originalRootLine A hd hs hp ho K i θ := by
    change CFSGNormalizerCenterAtoms.centerImage (P : Subgroup (Projective (cartan b₀ s₀) K))=_
    rw [hP]
    exact original_positive_center_eq_dominant_image A hd hs hp ho K p i θ hθ hdom
  obtain ⟨h,hh⟩ := CFSGOrthogonalDIndexSylowCenterFamily.exists_inner_centerImage_map p P
    (f * MulAut.conj g)
  rw [hcenter] at hh
  refine ⟨h,?_⟩
  change ((originalRootLine A hd hs hp ho K i θ).map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=_
  rw [Subgroup.map_map]
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamily
