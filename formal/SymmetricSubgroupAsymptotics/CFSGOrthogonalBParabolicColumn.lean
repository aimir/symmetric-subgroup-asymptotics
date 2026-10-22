import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveRadicalWords
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialFormGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount

/-! Concrete first elimination in the actual maximal-singular-space
stabilizer. Its middle column has no negative coordinates, and actual
short-root words clear its positive coordinates pointwise on V⁺. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicColumn
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBIndexForm CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBPositiveRadicalWords CFSGOrthogonalBSingularVectorCount
variable (K : Type) [Field K]

theorem pairing_positive (n : ℕ) (i : Fin n) (v : Index n → K) :
    (gram K n).toBilin' (Pi.single (pos n i) 1) v = 2 * v (neg n i) := by
  simp [Matrix.toBilin'_apply, gram, pos, neg, Fintype.sum_sum_type,
    Pi.single_apply, ite_mul]

theorem pairing_middle (n : ℕ) (v : Index n → K) :
    (gram K n).toBilin' v (Pi.single (middle n) 1) = v (middle n) := by
  simp [Matrix.toBilin'_apply, gram, middle, Fintype.sum_sum_type,
    Pi.single_apply, mul_ite]

theorem middle_column_negative_zero (h2 : (2 : K) ≠ 0) (n : ℕ)
    (g : formUnits K n)
    (hP : (positiveSubspace K n).map (Matrix.mulVecLin (g.val : Mat K n)) =
      positiveSubspace K n) :
    ∀ i, (((g.val : Mat K n) *ᵥ Pi.single (middle n) 1) (neg n i)) = 0 := by
  intro i
  have hi : (Pi.single (pos n i) 1 : Index n → K) ∈ positiveSubspace K n := by
    apply (mem_positiveSubspace K n _).mpr
    constructor
    · intro j
      simp [pos, neg]
    · simp [pos, middle]
  rw [← hP] at hi
  obtain ⟨v, hv, he⟩ := hi
  have hvm := ((mem_positiveSubspace K n v).mp hv).2
  have hp := pairing_invariant K n g v (Pi.single (middle n) 1)
  change (gram K n).toBilin' ((g.val : Mat K n) *ᵥ v)
    ((g.val : Mat K n) *ᵥ Pi.single (middle n) 1) = _ at hp
  change (g.val : Mat K n) *ᵥ v = Pi.single (pos n i) 1 at he
  rw [he, pairing_positive, pairing_middle, hvm] at hp
  exact (mul_eq_zero.mp hp).resolve_left h2

theorem exists_clear_middle (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : formUnits K (s + 1))
    (hP : (positiveSubspace K (s + 1)).map
      (Matrix.mulVecLin (g.val : Mat K (s + 1))) = positiveSubspace K (s + 1)) :
    ∃ a : elementaryRootGroup K (s + 1), ∃ c : K, c ≠ 0 ∧
      (∀ u ∈ positiveSubspace K (s + 1), (a.val : Mat K (s + 1)) *ᵥ u = u) ∧
      ((a.val : Mat K (s + 1)) * (g.val : Mat K (s + 1))) *ᵥ
        Pi.single (middle (s + 1)) 1 = c • Pi.single (middle (s + 1)) 1 := by
  let v : Index (s + 1) → K := (g.val : Mat K (s + 1)) *ᵥ
    Pi.single (middle (s + 1)) 1
  have hn := middle_column_negative_zero K h2 (s + 1) g hP
  have hnorm : (gram K (s + 1)).toBilin' v v = 1 := by
    change (gram K (s + 1)).toBilin'
      ((g.val : Mat K (s + 1)) *ᵥ Pi.single (middle (s + 1)) 1)
      ((g.val : Mat K (s + 1)) *ᵥ Pi.single (middle (s + 1)) 1) = 1
    rw [pairing_invariant K (s + 1) g]
    simp [gram, middle]
  have hc : v (middle (s + 1)) ≠ 0 := by
    intro hz
    have h0 : (gram K (s + 1)).toBilin' v v = 0 := by
      rw [gram_norm_dot]
      have hneg : CFSGOrthogonalBVectorCoordinates.negativePart K (s + 1) v = 0 :=
        funext hn
      simp [hneg, hz, CFSGParabolicQuadricCount.dotDual]
    exact zero_ne_one (h0.symm.trans hnorm)
  obtain ⟨a, hafix, ha⟩ := exists_clear_positive K s v hn hc
  refine ⟨a, v (middle (s + 1)), hc, hafix, ?_⟩
  rw [← Matrix.mulVec_mulVec]
  exact ha

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBParabolicColumn
