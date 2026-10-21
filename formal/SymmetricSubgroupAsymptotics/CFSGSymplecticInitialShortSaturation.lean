import SymmetricSubgroupAsymptotics.CFSGSymplecticFirstTorusShortExtraction

/-! Recovery of every actual first short-root parameter from the same
two initial elements over finite fields of order at least four. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def initialShortRootParameters (K : Type) [Field K] (r : ℕ)
    (H : Subgroup (elementaryRootGroup K (r + 1))) : AddSubgroup K where
  carrier := {a | initialShortRoot K r a ∈ H}
  zero_mem' := by
    change initialShortRoot K r 0 ∈ H
    rw [initialShortRoot_zero]
    exact H.one_mem
  add_mem' := by
    intro a b ha hb
    change initialShortRoot K r (a + b) ∈ H
    rw [initialShortRoot_add]
    exact H.mul_mem ha hb
  neg_mem' := by
    intro a ha
    change initialShortRoot K r (-a) ∈ H
    have he : initialShortRoot K r (-a) = (initialShortRoot K r a)⁻¹ := by
      symm
      apply inv_eq_of_mul_eq_one_right
      rw [← initialShortRoot_add, add_neg_cancel, initialShortRoot_zero]
    rw [he]
    exact H.inv_mem ha

theorem all_initialShort_parameters_of_firstTorus (K : Type) [Field K] [Finite K]
    (r : ℕ) (hr : 0 < r) (H : Subgroup (elementaryRootGroup K (r + 1))) (g : Kˣ)
    (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g) (hT : firstTorus K r g ∈ H)
    (m : K) (hm : m ≠ 0) (hM : initialShortRoot K r m ∈ H) :
    ∀ a : K, initialShortRoot K r a ∈ H := by
  let B := initialShortRootParameters K r H
  have hscale : ∀ a : K, a ∈ B → ((g⁻¹ : Kˣ) : K) * a ∈ B := by
    intro a ha
    change initialShortRoot K r (((g⁻¹ : Kˣ) : K) * a) ∈ H
    rw [Units.val_inv_eq_inv_val, ← firstTorus_short_conjugation K r hr]
    exact H.mul_mem (H.mul_mem hT ha) (H.inv_mem hT)
  have hpow : ∀ k : ℕ, m * ((g⁻¹ : Kˣ) : K) ^ k ∈ B := by
    intro k
    induction k with
    | zero => simpa only [pow_zero, mul_one] using hM
    | succ k ih =>
      have he : m * ((g⁻¹ : Kˣ) : K) ^ (k + 1) =
          ((g⁻¹ : Kˣ) : K) * (m * ((g⁻¹ : Kˣ) : K) ^ k) := by rw [pow_succ]; ring
      rw [he]
      exact hscale _ ih
  have hgi : ∀ u : Kˣ, u ∈ Subgroup.zpowers g⁻¹ := by
    intro u
    rw [Subgroup.zpowers_inv]
    exact hg u
  have he := CFSGFiniteFieldSquareSpan.eq_top_of_scaled_even_powers B g⁻¹ hgi m hm
    (fun k => hpow (2 * k))
  intro a
  have ha : a ∈ B := by rw [he]; trivial
  exact ha

theorem initial_pair_short_and_weyl (K : Type) [Field K] [Finite K]
    (hcard : 4 ≤ Nat.card K) (r : ℕ) (hr : 0 < r) (g : Kˣ)
    (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (H : Subgroup (elementaryRootGroup K (r + 1)))
    (hx : initialTorus K r g ∈ H) (hy : initialMixedWeyl K r ∈ H) :
    (∀ a : K, initialShortRoot K r a ∈ H) ∧ coxeterWeyl K r ∈ H := by
  obtain ⟨hY, hupper⟩ := initial_pair_cleaned_and_firstLong K hcard r hr g hg H hx hy
  have hlower := firstLowerLongRoot_mem_of_cleanMixed K r hr H hY hupper
  have hT := firstTorus_mem_of_long_lines K r H hupper hlower g
  have hg2 := CFSGTypeAPrimitiveUnitSquare.square_ne_one hcard g hg
  have hgn : (g : K) ≠ 1 := by intro h; apply hg2; rw [h, one_pow]
  have hgin : (g : K)⁻¹ ≠ 1 := by
    intro h
    apply hgn
    have hi := congrArg (fun x : K => x⁻¹) h
    simpa only [inv_inv, inv_one] using hi
  have hm : (1 - (g : K)) * (1 - (g : K)⁻¹) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hgn)) (sub_ne_zero.mpr (Ne.symm hgin))
  have hA := all_initialShort_parameters_of_firstTorus K r hr H g hg hT _ hm
    (initial_short_extraction_mem K r hr g H hT hY)
  refine ⟨hA, ?_⟩
  have hw := H.mul_mem (H.inv_mem (hA 1)) hY
  simpa only [cleanMixedWeyl, inv_mul_cancel_left] using hw

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
