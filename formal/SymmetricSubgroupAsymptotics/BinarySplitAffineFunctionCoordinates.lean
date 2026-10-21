import SymmetricSubgroupAsymptotics.BinaryPairSplitAffineRows
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerCoordinates
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

/-! Literal coordinates for full zero-offset models and their original
point-function action. Sparse stabilizer certificates can use these rows
without constructing a multiplication or an action table. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

/-- The actual inverse acts on the same original framed points. -/
theorem affinePermutation_inverse_apply_frame (t : Equiv.Perm (Fin w))
    (a : Fin w → ZMod 2) (i : Fin w) (b : ZMod 2) :
    (F.affinePermutation t a)⁻¹ (F.frame (i, b)) =
      F.frame (t.symm i, b - a i) := by
  apply (F.affinePermutation t a).injective
  rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply, F.affinePermutation_apply_frame,
    Equiv.apply_symm_apply, sub_add_cancel]

/-- The first coordinates are zero values; the second are pair sums.
The destination offset multiplies the transported pair sum. -/
def affinePairLayerMap (t : Equiv.Perm (Fin w)) (a : Fin w → ZMod 2) :
    ((Fin w → ZMod 2) × (Fin w → ZMod 2)) →ₗ[ZMod 2]
      ((Fin w → ZMod 2) × (Fin w → ZMod 2)) where
  toFun v := (fun i => v.1 (t.symm i) + a i * v.2 (t.symm i), fun i => v.2 (t.symm i))
  map_add' v z := by
    apply Prod.ext
    · funext i
      change (v.1 (t.symm i) + z.1 (t.symm i)) +
        a i * (v.2 (t.symm i) + z.2 (t.symm i)) =
          (v.1 (t.symm i) + a i * v.2 (t.symm i)) +
            (z.1 (t.symm i) + a i * z.2 (t.symm i))
      ring
    · rfl
  map_smul' c v := by
    apply Prod.ext
    · funext i
      change c * v.1 (t.symm i) + a i * (c * v.2 (t.symm i)) =
        c * (v.1 (t.symm i) + a i * v.2 (t.symm i))
      ring
    · rfl

/-- This is the original permutation-function action, including its
actual affine offset, expressed in reversible pair-layer coordinates. -/
theorem pairLayerCoordinateEquiv_affine_action
    (t : Equiv.Perm (Fin w)) (a : Fin w → ZMod 2) (f : X → ZMod 2) :
    F.pairLayerCoordinateEquiv (fun x => f ((F.affinePermutation t a)⁻¹ x)) =
      affinePairLayerMap t a (F.pairLayerCoordinateEquiv f) := by
  apply Prod.ext
  · funext i
    change f ((F.affinePermutation t a)⁻¹ (F.frame (i, 0))) = _
    rw [F.affinePermutation_inverse_apply_frame t a i 0,
      F.pair_value_eq_zero_add_sum f (t.symm i) (0 - a i)]
    simp only [zero_sub, CharTwo.neg_eq]
    rfl
  · funext i
    change f ((F.affinePermutation t a)⁻¹ (F.frame (i, 0))) +
      f ((F.affinePermutation t a)⁻¹ (F.frame (i, 1))) = F.pairSum f (t.symm i)
    rw [F.affinePermutation_inverse_apply_frame t a i 0,
      F.affinePermutation_inverse_apply_frame t a i 1,
      F.pair_value_eq_zero_add_sum f (t.symm i) (0 - a i),
      F.pair_value_eq_zero_add_sum f (t.symm i) (1 - a i)]
    rw [add_add_add_comm, CharTwo.add_self_eq_zero, zero_add, ← add_mul]
    have hc : (0 - a i) + (1 - a i) = (1 : ZMod 2) := by
      simp only [CharTwo.sub_eq_add, zero_add]
      rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    rw [hc, one_mul]

/-- The executable low/high bit convention used by sparse certificates. -/
def pairLayerFlatten : ((Fin w → ZMod 2) × (Fin w → ZMod 2)) ≃ₗ[ZMod 2]
    (Fin (w + w) → ZMod 2) where
  toFun v := Fin.append v.1 v.2
  invFun v := (fun i => v (Fin.castAdd w i), fun i => v (Fin.natAdd w i))
  left_inv v := by
    apply Prod.ext <;> funext i
    · exact Fin.append_left _ _ i
    · exact Fin.append_right _ _ i
  right_inv v := Fin.append_castAdd_natAdd
  map_add' v z := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right, Pi.add_apply, Prod.fst_add, Prod.snd_add]
  map_smul' c v := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]

/-- Every row consists of one actual kernel vector and one actual top
permutation. Both coordinates remain reversible. -/
def splitAffineCoordinateEquiv :
    (F.kernelSpace × F.top.range) ≃ F.SplitAffineModel where
  toFun v := ⟨Multiplicative.ofAdd v.1, v.2⟩
  invFun g := (g.left.toAdd, g.right)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reversible scalar/top row lists enumerate the whole original zero
model; no finite group table is required for completeness. -/
def splitAffineRowEquiv {q r : ℕ} (eK : Fin q ≃ F.kernelSpace)
    (eT : Fin r ≃ F.top.range) : (Fin q × Fin r) ≃ F.splitAffineAction :=
  ((eK.prodCongr eT).trans F.splitAffineCoordinateEquiv).trans F.splitAffineModelEquiv.toEquiv

theorem splitAffineRow_apply_frame {q r : ℕ} (eK : Fin q ≃ F.kernelSpace)
    (eT : Fin r ≃ F.top.range) (i : Fin q × Fin r) (j : Fin w) (b : ZMod 2) :
    (F.splitAffineRowEquiv eK eT i).val (F.frame (j, b)) =
      F.frame ((eT i.2).val j, b + (eK i.1).val ((eT i.2).val j)) := by
  exact F.affinePermutation_apply_frame _ _ _ _

end SymmetricSubgroupAsymptotics.BinaryPairFrame
