import SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicColumn

/-! Right-hand middle-column clearing in the actual positive-space
stabilizer. Surjectivity on that SAME space supplies the preimage; the
word fixes the whole positive space and needs no normality assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicRightClear
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBIndexForm CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBPositiveRadicalWords CFSGOrthogonalBParabolicColumn
open CFSGOrthogonalBSingularVectorCount
variable (K : Type) [Field K]

theorem exists_right_clear_middle (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : formUnits K (s + 1))
    (hP : (positiveSubspace K (s + 1)).map
      (Matrix.mulVecLin (g.val : Mat K (s + 1))) = positiveSubspace K (s + 1)) :
    ∃ b : elementaryRootGroup K (s + 1), ∃ c : K, c ≠ 0 ∧
      (∀ u ∈ positiveSubspace K (s + 1), (b.val : Mat K (s + 1)) *ᵥ u = u) ∧
      ((g.val : Mat K (s + 1)) * (b.val : Mat K (s + 1))) *ᵥ
        Pi.single (middle (s + 1)) 1 = c • Pi.single (middle (s + 1)) 1 := by
  let e : Index (s + 1) → K := Pi.single (middle (s + 1)) 1
  let v : Index (s + 1) → K := (g.val : Mat K (s + 1)) *ᵥ e
  let c := v (middle (s + 1))
  have hn : ∀ i, v (neg (s + 1) i) = 0 := middle_column_negative_zero K h2 (s + 1) g hP
  have hc2 : c ^ 2 = 1 := by
    have hh := pairing_invariant K (s + 1) g e e
    change (gram K (s + 1)).toBilin' v v = _ at hh
    rw [gram_norm_dot] at hh
    have hz : CFSGOrthogonalBVectorCoordinates.negativePart K (s + 1) v = 0 := funext hn
    simpa [hz, c, e, gram, middle, CFSGParabolicQuadricCount.dotDual] using hh
  have hc : c ≠ 0 := by intro hh; simp [hh] at hc2
  let u : Index (s + 1) → K := v - c • e
  have hu : u ∈ positiveSubspace K (s + 1) := by
    apply (mem_positiveSubspace K (s + 1) u).mpr
    constructor
    · intro i
      simpa [u, e, middle, neg] using hn i
    · simp [u, c, e, middle]
  have hminus : -u ∈ (positiveSubspace K (s + 1)).map
      (Matrix.mulVecLin (g.val : Mat K (s + 1))) := by
    rw [hP]
    exact (positiveSubspace K (s + 1)).neg_mem hu
  obtain ⟨w, hw, hgw⟩ := hminus
  obtain ⟨a, rfl⟩ := hw
  obtain ⟨b, hb⟩ := exists_positive_translation K s a
  refine ⟨b, c, hc, ?_, ?_⟩
  · intro z hz
    obtain ⟨hzn, hzm⟩ := (mem_positiveSubspace K (s + 1) z).mp hz
    rw [hb z hzn, hzm, zero_smul, add_zero]
  · have he : (b.val : Mat K (s + 1)) *ᵥ e = e + positiveEmbedding K (s + 1) a := by
      rw [hb e (fun i => by simp [e, middle, neg])]
      simp [e, middle]
    change (g.val : Mat K (s + 1)) *ᵥ positiveEmbedding K (s + 1) a = -u at hgw
    change ((g.val : Mat K (s + 1)) * (b.val : Mat K (s + 1))) *ᵥ e = c • e
    rw [← Matrix.mulVec_mulVec, he, Matrix.mulVec_add, hgw]
    change v + -(v - c • e) = c • e
    abel

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicRightClear
