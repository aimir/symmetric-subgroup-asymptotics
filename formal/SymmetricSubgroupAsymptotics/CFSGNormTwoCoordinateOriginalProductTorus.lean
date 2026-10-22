import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusHom
import SymmetricSubgroupAsymptotics.CFSGProductTorusAction

/-! The actual inner product torus in the same original projective group
realizes the literal Cartan scaling map on every positive simple root.
No prescribed diagonal automorphism is assumed to be inner. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProductTorus
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalRootDegree CFSGNormTwoCoordinateOriginalSimpleParameters
open CFSGNormTwoGeckTorusHom CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckDiagonalTorus CFSGNormTwoCoordinateRootTorusConjugation
open CFSGProductTorusAction CFSGIntegerMatrixPowerHom
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ j, A j j = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def elementaryTorusHom (j : Fin r) : Kˣ →* ElementaryGroup A hd hs hp ho K :=
  (parameterTorusHom A hs hp b₀ s₀ K j).codRestrict (ElementaryGroup A hd hs hp ho K)
    (fun t => by
      rw [parameterTorusHom_apply]
      exact (elementaryTorus A hd hs hp ho K j t).property)

theorem elementaryTorusHom_apply (j : Fin r) (t : Kˣ) :
    elementaryTorusHom A hd hs hp ho K j t = elementaryTorus A hd hs hp ho K j t :=
  Subtype.ext (parameterTorusHom_apply A hs hp b₀ s₀ K j t)

theorem elementary_tori_commute : Pairwise fun j k => ∀ t u,
    Commute (elementaryTorusHom A hd hs hp ho K j t) (elementaryTorusHom A hd hs hp ho K k u) := by
  intro j k _ t u
  rw [elementaryTorusHom_apply, elementaryTorusHom_apply]
  change _ * _ = _ * _
  apply Subtype.ext
  change parameterTorus A hs hp b₀ s₀ K j t * parameterTorus A hs hp b₀ s₀ K k u =
    parameterTorus A hs hp b₀ s₀ K k u * parameterTorus A hs hp b₀ s₀ K j t
  apply Units.ext
  simp only [Units.val_mul, torus_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

def originalTorusHom [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    Kˣ →* Projective (cartan b₀ s₀) K :=
  (originalProjection A hd hs hp ho K i).comp (elementaryTorusHom A hd hs hp ho K j)

theorem original_tori_commute [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Pairwise fun j k => ∀ t u,
      Commute (originalTorusHom A hd hs hp ho K i j t) (originalTorusHom A hd hs hp ho K i k u) := by
  intro j k hjk t u
  exact (elementary_tori_commute A hd hs hp ho K hjk t u).map
    (originalProjection A hd hs hp ho K i)

def originalProductTorusHom [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    (Fin r → Kˣ) →* Projective (cartan b₀ s₀) K :=
  productTorusHom (originalTorusHom A hd hs hp ho K i) (original_tori_commute A hd hs hp ho K i)

theorem original_torus_simple_action [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i j : Fin r) (t : Kˣ) (k : Fin r) (a : K) :
    originalTorusHom A hd hs hp ho K i j t *
      simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd a) *
        (originalTorusHom A hd hs hp ho K i j t)⁻¹ =
      simpleParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd (a * (t : K) ^ A k j)) := by
  have hpair : integerPairing A (s₀ j : Roots A).val (s₀ k : Roots A).val = A k j := by
    change integerPairing A (Pi.single j 1) (Pi.single k 1) = A k j
    simp only [integerPairing, Matrix.toBilin'_single]
    exact (congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M j k) hs).symm
  change originalProjection A hd hs hp ho K i (elementaryTorusHom A hd hs hp ho K j t) *
    originalSelectedHom A hd hs hp ho K i (s₀ k) _ (Multiplicative.ofAdd a) *
      (originalProjection A hd hs hp ho K i (elementaryTorusHom A hd hs hp ho K j t))⁻¹ = _
  rw [elementaryTorusHom_apply, originalSelectedHom_apply, simpleParameterHom, originalSelectedHom_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (originalProjection A hd hs hp ho K i)
  apply Subtype.ext
  simpa only [hpair] using torus_conjugate_selected_root A hd hs hp ho K j t (s₀ k) a

/-- Actual inner words realize every vector in the Cartan monomial image. -/
theorem original_product_torus_simple_action [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (x : Fin r → Kˣ) (j : Fin r) (a : K) :
    originalProductTorusHom A hd hs hp ho K i x *
      simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a) *
        (originalProductTorusHom A hd hs hp ho K i x)⁻¹ =
      simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd (a * (powerHom (G := Kˣ) A x j : K))) :=
  product_action (originalTorusHom A hd hs hp ho K i) (original_tori_commute A hd hs hp ho K i)
    A (simpleParameterHom A hd hs hp ho K i) (original_torus_simple_action A hd hs hp ho K i) x j a

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProductTorus
