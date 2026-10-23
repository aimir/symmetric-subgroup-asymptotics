import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalFlagIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeFunctionalFlag

/-! The negative counterpart of integral zero-root recovery. Actual
opposition reverses the weak grading flag, so the negative group meets
the reverse flag in exactly the opposition image of the zero-root
subgroup. This works for arbitrary supports in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeFunctionalIntersection
open CFSGGradedMatrixSupport CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits

private theorem conjugate_triangular {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (w : I → ℤ) (s g : (Matrix I I K)ˣ)
    (hs : Supported w (fun z => -z) (s : Matrix I I K))
    (hsi : Supported w (fun z => -z) (↑(s⁻¹) : Matrix I I K))
    (hg : g ∈ triangularUnits w) :
    s * g * s⁻¹ ∈ triangularUnits (fun i => -w i) := by
  intro i j hij
  change ((s : Matrix I I K) * (g : Matrix I I K) * (↑(s⁻¹) : Matrix I I K)) i j = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hkj : (↑(s⁻¹) : Matrix I I K) k j = 0
  · rw [hkj, mul_zero]
  · have hwkj : w k = -w j := by
      by_contra hne
      exact hkj (hsi k j hne)
    have hinner : ((s : Matrix I I K) * (g : Matrix I I K)) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : (s : Matrix I I K) i l = 0
      · rw [hil, zero_mul]
      · have hwil : w i = -w l := by
          by_contra hne
          exact hil (hs i l hne)
        have hglk : (g : Matrix I I K) l k = 0 := hg (by
          change -w j < -w i at hij
          omega)
        rw [hglk, mul_zero]
    rw [hinner, zero_mul]

open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateZeroFunctionalSupport CFSGNormTwoCoordinateFunctionalFlagIntersection
open CFSGNormTwoGeckFieldOpposition CFSGNormTwoGeckOppositionWeyl
open CFSGNormTwoGeckOppositionDegree CFSGNormTwoCoordinateOppositeNormalizerIntersection
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev Mat (K : Type) := Matrix ((b₀).support ⊕ Roots A) ((b₀).support ⊕ Roots A) K

omit [(rootPairing A hs hp).IsReduced] in
private theorem opposition_support (K : Type) [Field K] (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) :
    Supported (fun j => f (latticeWeight A hs hp b₀ j)) (fun z => -z)
      (oppositionUnit A hs hp b₀ K : Mat A hd hs hp ho K) := by
  intro i j hij
  apply opposition_lattice_support A hs hp b₀ K i j
  intro he
  apply hij
  change latticeWeight A hs hp b₀ i = -latticeWeight A hs hp b₀ j at he
  change f (latticeWeight A hs hp b₀ i) = -f (latticeWeight A hs hp b₀ j)
  rw [he, map_neg]

omit [(rootPairing A hs hp).IsReduced] in
theorem opposition_conjugate_flag (K : Type) [Field K]
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (g : (Mat A hd hs hp ho K)ˣ)
    (hg : g ∈ triangularUnits (fun j => f (latticeWeight A hs hp b₀ j))) :
    oppositionUnit A hs hp b₀ K * g * (oppositionUnit A hs hp b₀ K)⁻¹ ∈
      triangularUnits (fun j => -f (latticeWeight A hs hp b₀ j)) := by
  apply conjugate_triangular _ _ _ (opposition_support A hd hs hp ho K f) _ hg
  simpa only [opposition_inverse] using opposition_support A hd hs hp ho K f

theorem negative_inf_reverse_flag_eq_opposition_zero (K : Type) [Field K]
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (hf : ∀ k : PositiveRoot A, 0 ≤ f k.val.val) :
    rootGroup A hs hp b₀ s₀ K true ⊓
      triangularUnits (fun j => -f (latticeWeight A hs hp b₀ j)) =
        (zeroFunctionalGroup A hd hs hp ho K f).map
          (MulAut.conj (oppositionUnit A hs hp b₀ K)).toMonoidHom := by
  let e := (MulAut.conj (oppositionUnit A hs hp b₀ K)).toMonoidHom
  apply le_antisymm
  · rintro g ⟨hg, hflag⟩
    have hpos : e g ∈ rootGroup A hs hp b₀ s₀ K false :=
      opposition_conjugate_mem A hs hp b₀ s₀ K true g hg
    have hnegflag : g ∈ triangularUnits
        (fun j => (-f) (latticeWeight A hs hp b₀ j)) := by
      simpa only [LinearMap.neg_apply] using hflag
    have hposflag : e g ∈ triangularUnits (fun j => f (latticeWeight A hs hp b₀ j)) := by
      simpa only [LinearMap.neg_apply, neg_neg] using
        opposition_conjugate_flag A hd hs hp ho K (-f) g hnegflag
    have hzero : e g ∈ zeroFunctionalGroup A hd hs hp ho K f := by
      rw [← positive_inf_functional_flag_eq_zeroFunctionalGroup A hd hs hp ho K f hf]
      exact ⟨hpos, hposflag⟩
    refine ⟨e g, hzero, ?_⟩
    exact opposition_twice A hs hp b₀ K g
  · rintro _ ⟨g, hg, rfl⟩
    have htri : g ∈ triangularUnits (fun j => f (latticeWeight A hs hp b₀ j)) :=
      preserving_le_triangular _ (zeroFunctionalGroup_le_preserving A hd hs hp ho K f hg)
    exact ⟨opposition_conjugate_mem A hs hp b₀ s₀ K false g
      (zeroFunctionalGroup_le_positive A hd hs hp ho K f hg),
      opposition_conjugate_flag A hd hs hp ho K f g htri⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeFunctionalIntersection
