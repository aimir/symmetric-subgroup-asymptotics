import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeNormalizerIntersection

/-! The full opposite normalizer in the literal elementary group
preserves every weak flag from a nonnegative simple-root functional.
The diagonal residual is retained: no equality with a generated torus
or BN-pair is assumed. This extends the one-simple-root excluded-height
argument to arbitrary supports, including folded orthogonal pairs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeFunctionalFlag
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckArbitraryHeightSupport
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckQuadraticMembership
open CFSGNormTwoGeckOppositionDegree CFSGNormTwoGeckFieldOpposition
open CFSGNormTwoGeckOppositionWeyl CFSGGradedMatrixSupport CFSGGradedMatrixSubgroups
open CFSGGradedMatrixTriangularUnits CFSGNormTwoCoordinateNormalizerDiagonalFactor
open CFSGNormTwoCoordinateOppositeNormalizerIntersection CFSGSubgroupConjugateOrbitCardinality
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ j, A j j = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem negative_le_functional_triangular (K : Type) [Field K]
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (hf : ∀ i : Fin r, 0 ≤ f (s₀ i : Roots A).val) :
    rootGroup A hs hp b₀ s₀ K true ≤ triangularUnits (weight A hs hp b₀ f) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i, t⟩, rfl⟩
  have hpos := canonicalRoot_quadraticGrade A hs hp b₀ s₀ K i t
  have hneg := opposition_quadraticGrade A hs hp b₀ K (s₀ i : Roots A).val _ hpos
  rw [canonicalRoot_conjugate] at hneg
  rcases (hf i).eq_or_lt with hz | hstrict
  · apply preserving_le_triangular _
    exact quadratic_preserves A hs hp b₀ f K _ _ hneg (by rw [map_neg, ← hz, neg_zero])
  · have hmem := quadratic_strict A hs hp b₀ (-f) K _ _ hneg (by
      simp only [LinearMap.neg_apply, map_neg, neg_neg]
      exact hstrict)
    have he : weight A hs hp b₀ (-f) = (fun j => -weight A hs hp b₀ f j) := by
      funext j
      cases j <;> rfl
    rw [he] at hmem
    simpa only [neg_neg] using
      strict_le_reverse_triangular (fun j => -weight A hs hp b₀ f j) hmem

theorem opposition_diagonal_functional_preserving (K : Type) [Field K]
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ)
    (d : (Matrix ((b₀).support ⊕ Roots A) ((b₀).support ⊕ Roots A) K)ˣ)
    (hdiag : (d : Matrix ((b₀).support ⊕ Roots A) ((b₀).support ⊕ Roots A) K).IsDiag) :
    oppositionUnit A hs hp b₀ K * d * (oppositionUnit A hs hp b₀ K)⁻¹ ∈
      preservingUnits (weight A hs hp b₀ f) := by
  have hO : Supported (weight A hs hp b₀ f) (fun z => -z)
      (oppositionUnit A hs hp b₀ K : Matrix _ _ K) := by
    intro j k hjk
    apply opposition_lattice_support A hs hp b₀ K j k
    intro he
    apply hjk
    change CFSGNormTwoGeckLatticeDegree.latticeWeight A hs hp b₀ j =
      -CFSGNormTwoGeckLatticeDegree.latticeWeight A hs hp b₀ k at he
    have hh := congrArg f he
    simpa only [height_latticeWeight, map_neg] using hh
  have hOi : Supported (weight A hs hp b₀ f) (fun z => -z)
      (↑((oppositionUnit A hs hp b₀ K)⁻¹) : Matrix _ _ K) := by
    rwa [opposition_inverse]
  have hD : Supported (weight A hs hp b₀ f) id (d : Matrix _ _ K) := by
    intro j k hjk
    apply hdiag
    intro he
    subst k
    exact hjk rfl
  apply supported_congr (supported_mul (supported_mul hO hD) hOi)
  intro z
  exact neg_neg z

theorem negative_normalizer_le_functional_triangular (K : Type) [Field K]
    (epsilon : Fin r → ℤ) (hepsilon : ∀ j, epsilon j * epsilon j = 1)
    (hA : ∀ i j, epsilon i * |A i j| = A j i * epsilon j)
    (hidentity : ∀ w : List (Fin r), wordUnit A hs hp b₀ s₀ K w ∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) →
        wordLinear A hs hp b₀ s₀ w = 1)
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (hf : ∀ i : Fin r, 0 ≤ f (s₀ i : Roots A).val) :
    Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _) ⊓
      canonicalElementaryGroup D K ≤ triangularUnits (weight A hs hp b₀ f) := by
  intro g hg
  let e := (MulAut.conj (oppositionUnit A hs hp b₀ K)).toMonoidHom
  have hN := Subgroup.le_normalizer_map e ⟨g, hg.1, rfl⟩
  rw [opposition_negative_eq_positive A hd hs hp ho K] at hN
  have hH : e g ∈ canonicalElementaryGroup D K := by
    rw [← opposition_elementary_eq_elementary A hd hs hp ho K]
    exact ⟨g, hg.2, rfl⟩
  obtain ⟨u, hu, d, hdiag, he⟩ := normalizer_diagonal_factor A hd hs hp ho K
    epsilon hepsilon hA hidentity (e g) hH hN
  have hge : g = e u * e d := by
    calc
      g = e (e g) := (opposition_twice A hs hp b₀ K g).symm
      _ = e (u * d) := congrArg e he
      _ = e u * e d := map_mul e u d
  rw [hge]
  exact (triangularUnits (weight A hs hp b₀ f)).mul_mem
    (negative_le_functional_triangular A hd hs hp ho K f hf
      (opposition_conjugate_mem A hs hp b₀ s₀ K false u hu))
    (preserving_le_triangular _
      (opposition_diagonal_functional_preserving A hd hs hp ho K f d hdiag))

theorem negative_normalizer_le_functional_flag (K : Type) [Field K]
    (epsilon : Fin r → ℤ) (hepsilon : ∀ j, epsilon j * epsilon j = 1)
    (hA : ∀ i j, epsilon i * |A i j| = A j i * epsilon j)
    (hidentity : ∀ w : List (Fin r), wordUnit A hs hp b₀ s₀ K w ∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) →
        wordLinear A hs hp b₀ s₀ w = 1)
    (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (hf : ∀ i : Fin r, 0 ≤ f (s₀ i : Roots A).val) :
    Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _) ⊓
      canonicalElementaryGroup D K ≤ triangularUnits
        (fun j => f (CFSGNormTwoGeckLatticeDegree.latticeWeight A hs hp b₀ j)) := by
  have hw : (fun j => f (CFSGNormTwoGeckLatticeDegree.latticeWeight A hs hp b₀ j)) =
      weight A hs hp b₀ f := by
    funext j
    cases j <;> simp only [CFSGNormTwoGeckLatticeDegree.latticeWeight, weight, map_zero]
  rw [hw]
  exact negative_normalizer_le_functional_triangular A hd hs hp ho K
    epsilon hepsilon hA hidentity f hf

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeFunctionalFlag
