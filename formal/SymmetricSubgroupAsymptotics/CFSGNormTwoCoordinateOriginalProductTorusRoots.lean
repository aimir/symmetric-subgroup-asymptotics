import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProductTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleRootLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedGeneration

/-! The literal projected product torus preserves every original root
line, and hence both U and V. This verifies the actual inner lift needed
in the semilinear coset count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProductTorusRoots
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinateOriginalProductTorus
open CFSGNormTwoCoordinateOriginalSignedParameters CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGNormTwoCoordinateRootTorusConjugation CFSGNormTwoCoordinateOriginalSimpleParameters
open CFSGNormTwoCoordinateOriginalMixedA2Rigidity CFSGNormTwoCoordinateNegativeSimpleRootLine
open CFSGNormTwoCoordinateOriginalNormalizerIntersection CFSGNormTwoCoordinateOriginalComplementNormalizer
open CFSGNormTwoCoordinateOriginalPositiveCenter CFSGNormTwoCoordinateOriginalOppositeAlignment
open CFSGNormTwoCoordinateSignedGeneration CFSGProductTorusAction CFSGIntegerMatrixPowerHom
open CFSGFieldScaledRootHom CFSGNormTwoGeckColumns
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ j, A j j = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def rootCharacter (x : Fin r → Kˣ) (k : Roots A) : Kˣ :=
  ∏ j, x j ^ integerPairing A (s₀ j : Roots A).val k.val

theorem original_torus_root_action [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i j : Fin r) (t : Kˣ) (k : Roots A) (a : K) :
    originalTorusHom A hd hs hp ho K i j t * rootParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd a) *
      (originalTorusHom A hd hs hp ho K i j t)⁻¹ =
      rootParameterHom A hd hs hp ho K i k
        (Multiplicative.ofAdd (a * (t : K) ^ integerPairing A (s₀ j : Roots A).val k.val)) := by
  change originalProjection A hd hs hp ho K i (elementaryTorusHom A hd hs hp ho K j t) *
    originalProjection A hd hs hp ho K i (elementarySelectedRootHom A hd hs hp ho K k (Multiplicative.ofAdd a)) *
      (originalProjection A hd hs hp ho K i (elementaryTorusHom A hd hs hp ho K j t))⁻¹ = _
  rw [elementaryTorusHom_apply, ← map_inv, ← map_mul, ← map_mul]
  apply congrArg (originalProjection A hd hs hp ho K i)
  apply Subtype.ext
  exact torus_conjugate_selected_root A hd hs hp ho K j t k a

theorem original_product_torus_root_action [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (x : Fin r → Kˣ) (k : Roots A) (a : K) :
    originalProductTorusHom A hd hs hp ho K i x * rootParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd a) *
      (originalProductTorusHom A hd hs hp ho K i x)⁻¹ =
      rootParameterHom A hd hs hp ho K i k
        (Multiplicative.ofAdd (a * (rootCharacter A hd hs hp ho K x k : K))) := by
  let B : Matrix (Fin r) (Fin r) ℤ := fun _ j => integerPairing A (s₀ j : Roots A).val k.val
  exact product_action (originalTorusHom A hd hs hp ho K i) (original_tori_commute A hd hs hp ho K i)
    B (fun _ => rootParameterHom A hd hs hp ho K i k)
    (fun j t _ a => original_torus_root_action A hd hs hp ho K i j t k a) x i a

theorem original_product_torus_root_line [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (x : Fin r → Kˣ) (k : Roots A) :
    (originalFullRootLine A hd hs hp ho K i k).map
      (MulAut.conj (originalProductTorusHom A hd hs hp ho K i x)).toMonoidHom =
        originalFullRootLine A hd hs hp ho K i k := by
  rw [← rootParameterHom_range, ← MonoidHom.range_comp]
  let c := rootCharacter A hd hs hp ho K x k
  have he : (MulAut.conj (originalProductTorusHom A hd hs hp ho K i x)).toMonoidHom.comp
      (rootParameterHom A hd hs hp ho K i k) =
        scaledHom (rootParameterHom A hd hs hp ho K i k) (c : K) := by
    apply MonoidHom.ext
    intro a
    change originalProductTorusHom A hd hs hp ho K i x * rootParameterHom A hd hs hp ho K i k a *
      (originalProductTorusHom A hd hs hp ho K i x)⁻¹ =
      rootParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd ((c : K) * a.toAdd))
    have hh := original_product_torus_root_action A hd hs hp ho K i x k a.toAdd
    have hc : rootParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd (a.toAdd * (c : K))) =
        rootParameterHom A hd hs hp ho K i k (Multiplicative.ofAdd ((c : K) * a.toAdd)) :=
      congrArg (rootParameterHom A hd hs hp ho K i k)
        (congrArg Multiplicative.ofAdd (mul_comm a.toAdd (c : K)))
    exact hh.trans hc
  rw [he]
  exact scaledHom_range _ _ (Units.ne_zero c)

theorem original_product_torus_positive [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (x : Fin r → Kˣ) :
    (originalPositive A hd hs hp ho K i).map
      (MulAut.conj (originalProductTorusHom A hd hs hp ho K i x)).toMonoidHom =
        originalPositive A hd hs hp ho K i := by
  rw [original_positive_eq_iSup, Subgroup.map_iSup]
  congr 1
  funext j
  rw [originalSimpleRootGroup_eq_fullRootLine]
  exact original_product_torus_root_line A hd hs hp ho K i x (s₀ j)

theorem original_product_torus_negative [Finite K] [Nontrivial (Fin r)]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (x : Fin r → Kˣ) :
    (originalNegative A hd hs hp ho K i).map
      (MulAut.conj (originalProductTorusHom A hd hs hp ho K i x)).toMonoidHom =
        originalNegative A hd hs hp ho K i := by
  rw [original_negative_eq_iSup, Subgroup.map_iSup]
  congr 1
  funext j
  rw [← negativeParameterHom_range, negativeParameterHom, rootParameterHom_range]
  exact original_product_torus_root_line A hd hs hp ho K i x (negativeIndex A hs hp (s₀ j))

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProductTorusRoots
