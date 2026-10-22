import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveSimilitudes
import SymmetricSubgroupAsymptotics.CFSGSymplecticPointPairing
import SymmetricSubgroupAsymptotics.CFSGProjectiveSemilinearDecomposition

/-! Orthogonality-preserving finite-field collineations admit actual
similitude/field decompositions. The linear multiplier is derived from
zero-pairing preservation on the original vectors. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticCollineationSimilitudes
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry CFSGSymplecticPolarity
open CFSGProjectiveFrameCoordinates CFSGProjectiveFieldAction
variable {K : Type} [Field K]

def orthogonalGroup (n : ℕ) : Subgroup
    (collineationGroup (F := K) (n := Index n)) where
  carrier := {e | ∀ p q, Orthogonal K n (e.val p) (e.val q) ↔ Orthogonal K n p q}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro e f he hf p q
    exact (he (f.val p) (f.val q)).trans (hf p q)
  inv_mem' := by
    intro e he p q
    have h := he (e.val.symm p) (e.val.symm q)
    simpa only [Equiv.apply_symm_apply] using h.symm

theorem linear_pairing_zero_iff (n : ℕ)
    (a : (Index n → K) ≃ₗ[K] (Index n → K))
    (ha : ∀ p q, Orthogonal K n (linearPointEquiv a p) (linearPointEquiv a q) ↔
      Orthogonal K n p q) (v w : Index n → K) :
    pairing n (a v) (a w) = 0 ↔ pairing n v w = 0 := by
  by_cases hv : v = 0
  · subst v; simp only [map_zero, pairing_zero_left]
  by_cases hw : w = 0
  · subst w; simp only [map_zero, pairing_zero_right]
  have h := ha (Projectivization.mk K v hv) (Projectivization.mk K w hw)
  simpa only [linearPointEquiv_mk, CFSGSymplecticPointPairing.orthogonal_mk] using h

variable [Finite K]

theorem exists_similitude_decomposition (n : ℕ) (hn : 0 < n)
    (f : orthogonalGroup (K := K) n) (b i j : Index n)
    (hbi : b ≠ i) (hbj : b ≠ j) (hij : i ≠ j) :
    ∃ (g : CFSGSymplecticSimilitudeGroup.similitudes (K := K) n) (s : K ≃+* K),
      ∀ p, f.val.val p = CFSGSymplecticSimilitudeGroup.pointHom n g (pointEquiv s p) := by
  obtain ⟨a, s, has⟩ := CFSGProjectiveSemilinearDecomposition.exists_decomposition
    f.val b i j hbi hbj hij
  have ha (p q : ℙ K (Index n → K)) :
      Orthogonal K n (linearPointEquiv a p) (linearPointEquiv a q) ↔
        Orthogonal K n p q := by
    obtain ⟨x, rfl⟩ := (pointEquiv (n := Index n) s).surjective p
    obtain ⟨y, rfl⟩ := (pointEquiv (n := Index n) s).surjective q
    rw [← has x, ← has y]
    exact (f.property x y).trans (CFSGSymplecticPointPairing.fieldPoint_orthogonal n s x y).symm
  obtain ⟨c, hc, hform⟩ := CFSGSymplecticLinearSimilitudes.exists_multiplier n hn a
    (linear_pairing_zero_iff n a ha)
  let g : CFSGSymplecticSimilitudeGroup.similitudes (K := K) n := ⟨a, c, hc, hform⟩
  refine ⟨g, s, fun p => ?_⟩
  rw [has p]
  have hpoint (p : ℙ K (Index n → K)) :
      CFSGSymplecticSimilitudeGroup.pointHom n g p = linearPointEquiv a p := by
    induction p using Projectivization.ind with
    | h v hv => rfl
  exact (hpoint _).symm

end SymmetricSubgroupAsymptotics.CFSGSymplecticCollineationSimilitudes
