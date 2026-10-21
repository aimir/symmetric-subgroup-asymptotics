import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialLongSaturation

/-! Once the pure second long-root line is recovered, the same
original generating subgroup contains the cleaned short-root/Weyl word
and the complete first long-root line. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def cleanMixedWeyl (K : Type) [Field K] (r : ℕ) : elementaryRootGroup K (r + 1) :=
  initialShortRoot K r 1 * coxeterWeyl K r

theorem cleanMixedWeyl_mem (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hy : initialMixedWeyl K r ∈ H) (hB : secondLongRoot K r 1 ∈ H) :
    cleanMixedWeyl K r ∈ H := by
  have hc := (initial_root_lines_commute K r hr 1 1).symm.inv_left
  have he : (secondLongRoot K r 1)⁻¹ * initialMixedWeyl K r = cleanMixedWeyl K r := by
    unfold initialMixedWeyl cleanMixedWeyl
    calc
      _ = ((secondLongRoot K r 1)⁻¹ * initialShortRoot K r 1) *
          secondLongRoot K r 1 * coxeterWeyl K r := by group
      _ = (initialShortRoot K r 1 * (secondLongRoot K r 1)⁻¹) *
          secondLongRoot K r 1 * coxeterWeyl K r := by rw [hc.eq]
      _ = _ := by group
  rw [← he]
  exact H.mul_mem (H.inv_mem hB) hy

theorem cleanMixedWeyl_firstLong_conjugation (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (a : K) :
    (cleanMixedWeyl K r)⁻¹ * secondLongRoot K r a * cleanMixedWeyl K r = firstLongRoot K r a := by
  have hc := (initial_root_lines_commute K r hr 1 a).inv_left
  have he : (initialShortRoot K r 1)⁻¹ * secondLongRoot K r a * initialShortRoot K r 1 =
      secondLongRoot K r a := by
    rw [hc.eq]
    group
  unfold cleanMixedWeyl
  calc
    _ = (coxeterWeyl K r)⁻¹ *
        ((initialShortRoot K r 1)⁻¹ * secondLongRoot K r a * initialShortRoot K r 1) *
        coxeterWeyl K r := by group
    _ = (coxeterWeyl K r)⁻¹ * secondLongRoot K r a * coxeterWeyl K r := by rw [he]
    _ = firstLongRoot K r a := by rw [secondLongRoot]; group

theorem firstLongRoot_mem_of_cleanMixed (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hy : cleanMixedWeyl K r ∈ H) (hB : ∀ a : K, secondLongRoot K r a ∈ H) :
    ∀ a : K, firstLongRoot K r a ∈ H := by
  intro a
  rw [← cleanMixedWeyl_firstLong_conjugation K r hr]
  exact H.mul_mem (H.mul_mem (H.inv_mem hy) (hB a)) hy

theorem initial_pair_cleaned_and_firstLong (K : Type) [Field K] [Finite K]
    (hcard : 4 ≤ Nat.card K) (r : ℕ) (hr : 0 < r) (g : Kˣ)
    (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hx : initialTorus K r g ∈ H) (hy : initialMixedWeyl K r ∈ H) :
    cleanMixedWeyl K r ∈ H ∧ ∀ a : K, firstLongRoot K r a ∈ H := by
  have hB := all_secondLong_parameters_of_initial_pair K hcard r hr g hg H hx hy
  have hY := cleanMixedWeyl_mem K r hr H hy (hB 1)
  exact ⟨hY, firstLongRoot_mem_of_cleanMixed K r hr H hY hB⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
