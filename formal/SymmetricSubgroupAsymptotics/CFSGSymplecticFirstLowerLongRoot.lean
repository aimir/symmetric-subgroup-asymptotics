import SymmetricSubgroupAsymptotics.CFSGSymplecticCleanMixedWeyl

/-! The actual first lower long-root line and its torus word. Defining
it as a Weyl conjugate proves membership in the original elementary
group; membership in the two-generator subgroup is a separate step. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def firstLowerLongRoot (K : Type) [Field K] (r : ℕ) (a : K) : elementaryRootGroup K (r + 1) :=
  coxeterWeyl K r * elementaryRoot K (r + 1) false (Fin.last r) (-a) *
    (coxeterWeyl K r)⁻¹

theorem firstLowerLongRoot_coe (K : Type) [Field K] (r : ℕ) (a : K) :
    ((firstLowerLongRoot K r a).val : Mat K (r + 1)) =
      Matrix.transvection (Sum.inr (0 : Fin (r + 1))) (Sum.inl 0) a := by
  have h := coxeter_transvection_conjugation K r
    (elementaryRoot K (r + 1) false (Fin.last r) (-a))
    (Sum.inl (Fin.last r)) (Sum.inr (Fin.last r)) (by intro h; cases h) (-a)
    (terminal_positive_coe K r (-a))
  change ((firstLowerLongRoot K r a).val : Mat K (r + 1)) = _ at h
  rw [coxeterCycle_inl_last, coxeterCycle_inr_last] at h
  simp only [coxeterSign, if_true] at h
  have hc : (-1 : K) ^ r * (-a) / (-1 : K) ^ (r + 1) = a := by
    rw [pow_succ]
    field_simp <;> ring
  simpa only [hc] using h

/-- The original first torus is a four-root word at the first pair. -/
theorem firstTorus_root_word (K : Type) [Field K] (r : ℕ) (g : Kˣ) :
    firstTorus K r g =
      firstLongRoot K r ((g : K) - 1) * firstLowerLongRoot K r 1 *
        firstLongRoot K r ((g : K)⁻¹ - 1) * firstLowerLongRoot K r (-(g : K)) := by
  apply Subtype.ext
  apply Units.ext
  change ((firstTorus K r g).val : Mat K (r + 1)) =
    ((firstLongRoot K r ((g : K) - 1)).val : Mat K (r + 1)) *
      ((firstLowerLongRoot K r 1).val : Mat K (r + 1)) *
      ((firstLongRoot K r ((g : K)⁻¹ - 1)).val : Mat K (r + 1)) *
      ((firstLowerLongRoot K r (-(g : K))).val : Mat K (r + 1))
  rw [firstTorus_coe, firstLongRoot_coe, firstLowerLongRoot_coe,
    firstLongRoot_coe, firstLowerLongRoot_coe]
  exact (CFSGTypeAElementaryMatrices.diagonal_pair
    (show (Sum.inl (0 : Fin (r + 1)) : Index (r + 1)) ≠ Sum.inr 0 by intro h; cases h)
    (g : K) (Units.ne_zero g)).symm

theorem firstTorus_mem_of_long_lines (K : Type) [Field K] (r : ℕ)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hupper : ∀ a : K, firstLongRoot K r a ∈ H)
    (hlower : ∀ a : K, firstLowerLongRoot K r a ∈ H) (g : Kˣ) :
    firstTorus K r g ∈ H := by
  rw [firstTorus_root_word]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hupper _) (hlower _)) (hupper _)) (hlower _)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
