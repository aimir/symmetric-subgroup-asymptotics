import SymmetricSubgroupAsymptotics.CFSGSymplecticSignedLongCoverage
import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialShortSaturation

/-! The complete actual elementary C group is recovered from its two
initial full root lines and the actual Coxeter word. This theorem is
uniform in characteristic and uses the original simple-root generator
set, without identifying the group with the full symplectic group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGActualMatrixRootLines

private theorem elementary_eq_top_initial_lines_succ (K : Type) [Field K] (s : ℕ)
    (H : Subgroup (elementaryRootGroup K (s + 2)))
    (hW : coxeterWeyl K (s + 1) ∈ H)
    (hA : ∀ a : K, initialShortRoot K (s + 1) a ∈ H)
    (hB : ∀ a : K, secondLongRoot K (s + 1) a ∈ H) : H = ⊤ := by
  let H' := H.map (elementaryRootGroup K (s + 2)).subtype
  have hW' : (coxeterWeyl K (s + 1)).val ∈ H' := ⟨_, hW, rfl⟩
  have hA0 : HasRootLine H' (signedChainRoot K (s + 1) false (0 : Fin (s + 1))) := by
    intro a
    refine ⟨(initialShortRoot K (s + 1) a).val, ⟨_, hA a, rfl⟩, ?_⟩
    change ((initialShortRoot K (s + 1) a).val : Mat K (s + 2)) =
      1 + a • initialShortMatrix K (s + 1) (by omega)
    exact initialShortRoot_coe K (s + 1) (by omega) a
  have hshort := signed_short_coverage K s H' hW' hA0
  have hY : cleanMixedWeyl K (s + 1) ∈ H := H.mul_mem (hA 1) hW
  have hupper := firstLongRoot_mem_of_cleanMixed K (s + 1) (by omega) H hY hB
  have hL0 : HasRootLine H' (coordinateLongRootMatrix K (s + 1) false 0) := by
    intro a
    refine ⟨(firstLongRoot K (s + 1) a).val, ⟨_, hupper a, rfl⟩, ?_⟩
    simpa only [coordinateLongRootMatrix, coordinatePoint, Bool.not_false,
      Bool.false_eq_true, if_false, if_true, Matrix.transvection,
      Matrix.smul_single, smul_eq_mul, mul_one] using firstLongRoot_coe K (s + 1) a
  have hlong := coordinate_long_coverage K (s + 1) H' hW' hL0
  have hroot : ∀ (neg : Bool) (i : Fin (s + 2)),
      HasRootLine H' (rootMatrix K (s + 2) neg i) := by
    intro neg i
    by_cases hi : i.val < s + 1
    · let k : Fin (s + 1) := ⟨i.val, hi⟩
      have hk : k.castSucc = i := Fin.ext rfl
      cases neg
      · apply hasRootLine_smul H' (rootMatrix K (s + 2) false i) (-1 : K)
          (neg_ne_zero.mpr one_ne_zero)
        simpa only [signedChainRoot_true, hk, neg_one_smul] using hshort true k
      · simpa only [signedChainRoot_false, hk] using hshort false k
    · have he : i = Fin.last (s + 1) := by
        apply Fin.ext
        have hb := i.isLt
        change i.val = s + 1
        omega
      subst i
      cases neg
      · simpa [coordinateLongRootMatrix, coordinatePoint, rootMatrix, positive] using
          hlong false (Fin.last (s + 1))
      · simpa [coordinateLongRootMatrix, coordinatePoint, rootMatrix, negative,
          positive, Matrix.transpose_single] using hlong true (Fin.last (s + 1))
  have hmem : ∀ (neg : Bool) (i : Fin (s + 2)) (a : K), elementaryRoot K (s + 2) neg i a ∈ H := by
    intro neg i a
    obtain ⟨u, hu, he⟩ := hroot neg i a
    have hue : u = (elementaryRoot K (s + 2) neg i a).val := Units.ext he
    have hm : (elementaryRoot K (s + 2) neg i a).val ∈ H' := hue ▸ hu
    obtain ⟨v, hv, hvu⟩ := hm
    exact (Subtype.ext hvu : v = elementaryRoot K (s + 2) neg i a) ▸ hv
  apply top_unique
  rw [← elementaryRootSet_generate K (s + 2)]
  apply (Subgroup.closure_le H).mpr
  rintro u ⟨neg, i, a, rfl⟩
  exact hmem neg i a

theorem elementary_eq_top_of_initial_root_lines (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hW : coxeterWeyl K r ∈ H)
    (hA : ∀ a : K, initialShortRoot K r a ∈ H)
    (hB : ∀ a : K, secondLongRoot K r a ∈ H) : H = ⊤ := by
  cases r with
  | zero => omega
  | succ s => exact elementary_eq_top_initial_lines_succ K s H hW hA hB

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
