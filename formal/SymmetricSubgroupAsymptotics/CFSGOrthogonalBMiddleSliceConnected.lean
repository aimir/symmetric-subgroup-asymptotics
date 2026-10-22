import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNonzeroMiddleCommonNeighbour
import SymmetricSubgroupAsymptotics.CFSGTwoFunctionalKernelVector

/-! The original singular vectors with middle coordinate one form an
orthogonality graph of diameter at most three in rank at least three.
Antipodes are handled by a three-edge path, not a false common-neighbour
assertion. The proof is uniform over all odd finite fields, including F3. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleSliceConnected
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBIntrinsicLongRoots CFSGOrthogonalBParabolicColumn
open CFSGOrthogonalBNonzeroMiddleCommonNeighbour
variable (K : Type) [Field K] [Finite K]

def Slice (s : ℕ) := {v : Index (s + 3) → K //
  (gram K (s + 3)).toBilin' v v = 0 ∧ v (middle (s + 3)) = 1}

theorem antipode_involutive (n : ℕ) (v : Index n → K) :
    antipode K n (antipode K n v) = v := by
  unfold antipode
  abel

theorem exists_three_edge_path (h2 : (2 : K) ≠ 0) (s : ℕ) (v w : Slice K s) :
    ∃ u t : Slice K s,
      (gram K (s + 3)).toBilin' v.val u.val = 0 ∧
      (gram K (s + 3)).toBilin' u.val t.val = 0 ∧
      (gram K (s + 3)).toBilin' t.val w.val = 0 := by
  let B := (gram K (s + 3)).toBilin'
  have hs (x y : Index (s + 3) → K) : B x y = B y x := gram_pairing_symmetric (s + 3) x y
  have hvv : B v.val v.val = 0 := v.property.1
  by_cases hvw : B v.val w.val = 0
  · exact ⟨v, v, v.property.1, v.property.1, hvw⟩
  by_cases hwanti : w.val = antipode K (s + 3) v.val
  · have hP : 3 ≤ Module.finrank K (positiveSubspace K (s + 3)) := by
      rw [positiveSubspace_finrank]
      omega
    obtain ⟨z, hzP, hz, hvz, _⟩ :=
      CFSGTwoFunctionalKernelVector.exists_nonzero_common_kernel
        (positiveSubspace K (s + 3)) hP (B v.val) 0
    have hzz : B z z = 0 := positiveSubspace_singular K (s + 3) z hzP z hzP
    have hzm : z (middle (s + 3)) = 0 := ((mem_positiveSubspace K (s + 3) z).mp hzP).2
    let u : Slice K s := ⟨v.val + z, by
      constructor
      · change B (v.val + z) (v.val + z) = 0
        simp only [map_add, LinearMap.add_apply, hvv, hzz,
          hvz, hs z v.val, add_zero, zero_add]
      · change v.val (middle (s + 3)) + z (middle (s + 3)) = 1
        rw [v.property.2, hzm, add_zero]⟩
    have hvu : B v.val u.val = 0 := by
      change B v.val (v.val + z) = 0
      rw [map_add, v.property.1, hvz, add_zero]
    have huv : B u.val v.val = 0 := (hs u.val v.val).trans hvu
    have huanti : w.val ≠ antipode K (s + 3) u.val := by
      intro hh
      have he : antipode K (s + 3) v.val = antipode K (s + 3) u.val := hwanti.symm.trans hh
      have he' := congrArg (antipode K (s + 3)) he
      rw [antipode_involutive, antipode_involutive] at he'
      have hz0 : z = 0 := by
        have hh' : v.val = v.val + z := he'
        exact (add_left_cancel (hh'.symm.trans (add_zero v.val).symm))
      exact hz hz0
    have huw : B u.val w.val = 2 := by
      rw [hwanti]
      unfold antipode
      rw [map_sub, map_smul, smul_eq_mul, pairing_middle K (s + 3) u.val,
        u.property.2, huv, mul_one, sub_zero]
    have huw0 : B u.val w.val ≠ 0 := fun hh => h2 (huw.symm.trans hh)
    obtain ⟨t, ht, htm, hut, hwt⟩ := exists_common_neighbour K h2 s u.val w.val
      u.property.1 w.property.1 u.property.2 w.property.2 huw0 huanti
    exact ⟨u, ⟨t, ht, htm⟩, hvu, hut, (hs t w.val).trans hwt⟩
  · obtain ⟨t, ht, htm, hvt, hwt⟩ := exists_common_neighbour K h2 s v.val w.val
      v.property.1 w.property.1 v.property.2 w.property.2 hvw hwanti
    exact ⟨v, ⟨t, ht, htm⟩, v.property.1, hvt, (hs t w.val).trans hwt⟩

theorem constant_of_orthogonal_edges {S : Type*} (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : Slice K s → S)
    (hf : ∀ v w, (gram K (s + 3)).toBilin' v.val w.val = 0 → f v = f w)
    (v w : Slice K s) : f v = f w := by
  obtain ⟨u, t, hvu, hut, htw⟩ := exists_three_edge_path K h2 s v w
  exact (hf v u hvu).trans ((hf u t hut).trans (hf t w htw))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleSliceConnected
