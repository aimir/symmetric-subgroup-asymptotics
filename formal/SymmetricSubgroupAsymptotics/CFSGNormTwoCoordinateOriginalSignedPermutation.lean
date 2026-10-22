import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedSimple
import SymmetricSubgroupAsymptotics.CFSGSignedRootPermutationAgreement
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementNormalizer

/-! The positive and negative literal simple-root permutations of one
original automorphism agree. The detection uses actual source-root
commutation and noncommutation, including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedPermutation
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoCoordinateOriginalPositiveCenter CFSGNormTwoCoordinateOriginalOppositeAlignment
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGNormTwoCoordinateOriginalSignedSimple CFSGSignedRootPermutationAgreement
open CFSGNormTwoCoordinateOriginalNormalizerIntersection
open CFSGNormTwoCoordinateOriginalComplementNormalizer

theorem originalSimpleHom_positive_range [Finite K] [Nontrivial (Fin r)]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    (originalSimpleHom A hd hs hp ho K i false j).range =
      originalSimpleRootGroup A hd hs hp ho K i j := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨elementarySimpleHom A hd hs hp ho K false j a, ⟨a.toAdd, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨a, ha⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    change originalProjection A hd hs hp ho K i (elementarySimpleHom A hd hs hp ho K false j _) = _
    apply congrArg (originalProjection A hd hs hp ho K i)
    exact Subtype.ext ha

 theorem originalSimpleHom_negative_range [Finite K] [Nontrivial (Fin r)]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    (originalSimpleHom A hd hs hp ho K i true j).range =
      originalNegativeSimpleRootGroup A hd hs hp ho K i j := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨elementarySimpleHom A hd hs hp ho K true j a, ⟨a.toAdd, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨a, ha⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    change originalProjection A hd hs hp ho K i (elementarySimpleHom A hd hs hp ho K true j _) = _
    apply congrArg (originalProjection A hd hs hp ho K i)
    exact Subtype.ext ha

 theorem simple_signed_permutations_agree [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (hdisj : originalPositive A hd hs hp ho K i ⊓ originalNegative A hd hs hp ho K i = ⊥)
    (f : MulAut (Projective (cartan b₀ s₀) K)) (σ τ : Equiv.Perm (Fin r))
    (hpos : ∀ j, (originalSimpleRootGroup A hd hs hp ho K i j).map f.toMonoidHom =
      originalSimpleRootGroup A hd hs hp ho K i (σ j))
    (hneg : ∀ j, (originalNegativeSimpleRootGroup A hd hs hp ho K i j).map f.toMonoidHom =
      originalNegativeSimpleRootGroup A hd hs hp ho K i (τ j)) : σ = τ := by
  refine permutations_agree (originalSimpleHom A hd hs hp ho K i false)
    (originalSimpleHom A hd hs hp ho K i true) ?_ ?_ f σ τ ?_ ?_
  · intro j k hjk a b
    exact opposite_distinct_indices_commute A hd hs hp ho K i j k hjk a b
  · intro j
    exact ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 1,
      same_index_not_commute A hd hs hp ho K p i j hdisj⟩
  · intro j
    simpa only [originalSimpleHom_positive_range] using hpos j
  · intro j
    simpa only [originalSimpleHom_negative_range] using hneg j

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSignedPermutation
