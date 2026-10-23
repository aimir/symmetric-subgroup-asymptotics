import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateZeroFunctionalSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNonnegativeHeightFlag

/-! A nonnegative integral root grading recognizes its zero-root subgroup
by intersecting the actual positive group with the opposite weak flag.
The same recognition holds for every intermediate subgroup contained in
that flag and containing the literal zero-root subgroup. No field-size,
BN-pair, or fixed-point lifting hypothesis is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalFlagIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateZeroFunctionalSupport CFSGNormTwoGeckNonnegativeHeightFlag
open CFSGNormTwoGeckArbitraryHeightSupport CFSGNormTwoGeckHeightSupport
open CFSGGradedMatrixSubgroups
open CFSGGradedMatrixTriangularUnits
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev Mat (K : Type) := Matrix ((b₀).support ⊕ Roots A) ((b₀).support ⊕ Roots A) K

theorem positive_le_reverse_functional_flag (K : Type) [Field K]
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (hf : ∀ k : PositiveRoot A, 0 ≤ f k.val.val) :
    rootGroup A hs hp b₀ s₀ K false ≤
      triangularUnits (fun j => -f (latticeWeight A hs hp b₀ j)) := by
  have hsimple : ∀ i : Fin r, 0 ≤ f (s₀ i : Roots A).val := by
    intro i
    apply hf ⟨s₀ i, ?_⟩
    intro j
    change 0 ≤ (Pi.single i (1 : ℤ) : Fin r → ℤ) j
    simp only [Pi.single_apply]
    split_ifs <;> omega
  have hw : (fun j => -f (latticeWeight A hs hp b₀ j)) =
      (fun j => -weight A hs hp b₀ f j) := by
    funext j
    cases j <;> simp only [latticeWeight, weight, map_zero]
  rw [hw]
  exact positive_le_reverse_triangular A hs hp b₀ s₀ f hsimple K

theorem positive_inf_functional_flag_eq_zeroFunctionalGroup (K : Type) [Field K]
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (hf : ∀ k : PositiveRoot A, 0 ≤ f k.val.val) :
    rootGroup A hs hp b₀ s₀ K false ⊓
      triangularUnits (fun j => f (latticeWeight A hs hp b₀ j)) =
        zeroFunctionalGroup A hd hs hp ho K f := by
  apply le_antisymm
  · intro g hg
    apply positive_mem_zeroFunctionalGroup_of_preserving A hd hs hp ho K f hf g hg.1
    exact (triangular_inf_reverse_eq_preserving
      (fun j => f (latticeWeight A hs hp b₀ j))).le
        ⟨hg.2, positive_le_reverse_functional_flag A hd hs hp ho K f hf hg.1⟩
  · exact le_inf (zeroFunctionalGroup_le_positive A hd hs hp ho K f)
      ((zeroFunctionalGroup_le_preserving A hd hs hp ho K f).trans
        (preserving_le_triangular _))

theorem positive_inf_intermediate_eq_zeroFunctionalGroup (K : Type) [Field K]
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (hf : ∀ k : PositiveRoot A, 0 ≤ f k.val.val)
    (H : Subgroup (Mat A hd hs hp ho K)ˣ)
    (hLH : zeroFunctionalGroup A hd hs hp ho K f ≤ H)
    (hHT : H ≤ triangularUnits (fun j => f (latticeWeight A hs hp b₀ j))) :
    rootGroup A hs hp b₀ s₀ K false ⊓ H = zeroFunctionalGroup A hd hs hp ho K f := by
  apply le_antisymm
  · exact (inf_le_inf_left _ hHT).trans
      (positive_inf_functional_flag_eq_zeroFunctionalGroup A hd hs hp ho K f hf).le
  · exact le_inf (zeroFunctionalGroup_le_positive A hd hs hp ho K f) hLH

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalFlagIntersection
