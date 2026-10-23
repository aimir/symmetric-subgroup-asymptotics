import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeTailEmbedding
import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFieldTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalQuadraticTwist

/-! The exact last-fork diagram--field twist commutes with omission of
the first hyperbolic pair. Fixedness descends to the literal tail unit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDTailTwist
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDIndexTailCoordinates CFSGTwistedDNaturalFork
open CFSGTwistedDNaturalFieldTwist CFSGTwistedDNaturalQuadraticTwist
variable (K : Type) [Field K]

theorem flip_tailIndex (n : ℕ) (i : Index (n + 2)) :
    CFSGOrthogonalDGenerationForkTorus.flip (n + 1) (tailIndex (n + 2) i) =
      tailIndex (n + 2) (CFSGOrthogonalDGenerationForkTorus.flip n i) := by
  have hl : (last n).succ = last (n + 1) := CFSGTwistedDRelativeTailEmbedding.last_succ n
  cases i with
  | inl i =>
    change CFSGOrthogonalDGenerationForkTorus.flip (n + 1) (Sum.inl i.succ) = _
    rw [flip_pos, flip_pos]
    by_cases hi : i = last n
    · subst i
      simp only [hl, if_true, tailIndex]
    · have hs : i.succ ≠ last (n + 1) := by
        rw [← hl]
        exact fun h => hi (Fin.succ_injective (n + 2) h)
      simp only [if_neg hi, if_neg hs, tailIndex]
  | inr i =>
    change CFSGOrthogonalDGenerationForkTorus.flip (n + 1) (Sum.inr i.succ) = _
    rw [flip_neg, flip_neg]
    by_cases hi : i = last n
    · subst i
      simp only [hl, if_true, tailIndex]
    · have hs : i.succ ≠ last (n + 1) := by
        rw [← hl]
        exact fun h => hi (Fin.succ_injective (n + 2) h)
      simp only [if_neg hi, if_neg hs, tailIndex]

theorem vectorTwist_tail (n : ℕ) (σ : K ≃+* K) (v : Index (n + 3) → K) :
    vectorTwist K n σ (v ∘ tailIndex (n + 2)) =
      vectorTwist K (n + 1) σ v ∘ tailIndex (n + 2) := by
  funext i
  change σ (v (tailIndex (n + 2) (CFSGOrthogonalDGenerationForkTorus.flip n i))) =
    σ (v (CFSGOrthogonalDGenerationForkTorus.flip (n + 1) (tailIndex (n + 2) i)))
  rw [flip_tailIndex]

theorem matrixTwist_tail (n : ℕ) (σ : K ≃+* K) (A : Mat K (n + 3)) :
    matrixTwist K n σ (A.submatrix (tailIndex (n + 2)) (tailIndex (n + 2))) =
      (matrixTwist K (n + 1) σ A).submatrix (tailIndex (n + 2)) (tailIndex (n + 2)) := by
  have hs (m : ℕ) : (CFSGOrthogonalDGenerationForkTorus.flip m).symm =
      CFSGOrthogonalDGenerationForkTorus.flip m := Equiv.symm_swap _ _
  ext i j
  change σ (A (tailIndex (n + 2) ((CFSGOrthogonalDGenerationForkTorus.flip n).symm i))
      (tailIndex (n + 2) ((CFSGOrthogonalDGenerationForkTorus.flip n).symm j))) =
    σ (A ((CFSGOrthogonalDGenerationForkTorus.flip (n + 1)).symm (tailIndex (n + 2) i))
      ((CFSGOrthogonalDGenerationForkTorus.flip (n + 1)).symm (tailIndex (n + 2) j)))
  simp only [hs, flip_tailIndex]

theorem fixed_tail_of_fixed_extension (n : ℕ) (σ : K ≃+* K) (a : (Mat K (n + 2))ˣ)
    (ha : unitTwist K (n + 1) σ (tailUnitHom K (n + 2) a) = tailUnitHom K (n + 2) a) :
    unitTwist K n σ a = a := by
  have hm := congrArg (fun u : (Mat K (n + 3))ˣ => (u : Mat K (n + 3))) ha
  change matrixTwist K (n + 1) σ (tailMatrixHom K (n + 2) (a : Mat K (n + 2))) =
    tailMatrixHom K (n + 2) (a : Mat K (n + 2)) at hm
  have he : (tailMatrixHom K (n + 2) (a : Mat K (n + 2))).submatrix
      (tailIndex (n + 2)) (tailIndex (n + 2)) = (a : Mat K (n + 2)) := by
    ext i j
    exact tailMatrixHom_tail_tail K (n + 2) _ i j
  have h := congrArg (fun M : Mat K (n + 3) =>
    M.submatrix (tailIndex (n + 2)) (tailIndex (n + 2))) hm
  dsimp only at h
  rw [← matrixTwist_tail, he] at h
  apply Units.ext
  exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedDTailTwist
