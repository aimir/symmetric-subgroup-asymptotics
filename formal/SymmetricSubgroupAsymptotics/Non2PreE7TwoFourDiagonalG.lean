import SymmetricSubgroupAsymptotics.Non2PreE7TwoFourDiagonalCS

/-!
# The class `Xg`

`Xg` has three minimal normal subgroups `Δ_e = {(v, cᵉ v c⁻ᵉ)}`, where
`c = (1 2 3)`.  The element `(1, c⁻ᵉ)` of `S₄ ≀ C₂` normalizes `Xg`; composed
with the diagonal projection it maps `Xg` onto `S₄` with kernel `Δ_e`.  A
nonzero base vector of a normal subgroup, multiplied by its conjugate under
`τ s`, has both coordinates nonzero, hence lies in one `Δ_e`, and the
rotations by `a` fill `Δ_e`.

`Xg'' = V`, so `Xg` is a binary cyclic-dual target on the common source `J''`.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace TwoFourDiagonal

open Equiv NaturalS4 C2Wreath SemidirectProduct

/-- The local three-cycle `c = (1 2 3)`. -/
def cLoc : Perm (Fin 4) := swap 1 2 * swap 2 3

/-- `dₑ = c⁻ᵉ`. -/
def dE (e : Fin 3) : Perm (Fin 4) := (cLoc ^ (e : ℕ))⁻¹

theorem dE_even : ∀ e : Fin 3, dE e ∈ a4Set ∧ (dE e)⁻¹ ∈ a4Set := by decide

theorem conj_pair_one : ∀ e : Fin 3, ∀ x1 x2 : Perm (Fin 4), x1 ∈ a4Set →
    pairFun x1 = pairFun x2 → pairFun x1 = pairFun (dE e * x2 * (dE e)⁻¹) := by decide +kernel

theorem conj_pair_gen : ∀ e : Fin 3, ∀ x1 x2 : Perm (Fin 4), x1 ∉ a4Set →
    pairFun x1 = pairFun x2 → pairFun (x1 * (dE e)⁻¹) = pairFun (dE e * x2) := by decide +kernel

theorem c_rotates : ∀ u1 ∈ kleinSet, u1 ≠ 1 → ∀ u2 ∈ kleinSet, u2 ≠ 1 →
    ∃ e : Fin 3, u2 = (dE e)⁻¹ * u1 * dE e := by decide +kernel

theorem t3_c_commute : ∀ u ∈ kleinSet, ∀ k : Fin 3, ∀ e : Fin 3,
    t3 ^ (k : ℕ) * ((dE e)⁻¹ * u * dE e) * (t3 ^ (k : ℕ))⁻¹ =
      (dE e)⁻¹ * (t3 ^ (k : ℕ) * u * (t3 ^ (k : ℕ))⁻¹) * dE e := by decide +kernel

theorem dE_conj_klein : ∀ e : Fin 3, ∀ u ∈ kleinSet, (dE e)⁻¹ * u * dE e ∈ kleinSet := by
  decide +kernel

theorem dE_conj_ne_one : ∀ e : Fin 3, ∀ u ∈ kleinSet, u ≠ 1 → (dE e)⁻¹ * u * dE e ≠ 1 := by
  decide +kernel

/-! ## Conjugation by `(1, dₑ)` -/

/-- `mₑ = (1, dₑ)`. -/
def mE (e : Fin 3) : W4 := inl (1, dE e)

theorem conj_mE_left (e : Fin 3) (x : W4) :
    (mE e * x * (mE e)⁻¹).left = (1, dE e) * x.left * swapAut _ x.right (1, (dE e)⁻¹) := by
  rw [mE, ← map_inv, mul_left', mul_left', left_inl, right_inl, swapAut_one, mul_right,
    right_inl, one_mul, left_inl]
  rfl

theorem conj_mE_right (e : Fin 3) (x : W4) : (mE e * x * (mE e)⁻¹).right = x.right := by
  rw [mE, ← map_inv, mul_right, mul_right, right_inl, right_inl, one_mul, mul_one]

theorem conj_mE_mem (e : Fin 3) (x : W4) (hx : x ∈ Xg) : mE e * x * (mE e)⁻¹ ∈ Xg := by
  obtain ⟨hxs, hxp⟩ := hx
  have hpair : pairFun x.left.1 = pairFun x.left.2 := (pairing_eq_iff _ _).mp hxs
  rcases C2Wreath.cases x.right with h | h
  · have hl : (mE e * x * (mE e)⁻¹).left = (x.left.1, dE e * x.left.2 * (dE e)⁻¹) := by
      rw [conj_mE_left, h, swapAut_one]
      exact Prod.ext (by simp) (by simp)
    have he : x.left.1 ∈ a4Set := hxp.mpr h
    refine ⟨?_, ?_⟩
    · show pairing (mE e * x * (mE e)⁻¹).left.1 = pairing (mE e * x * (mE e)⁻¹).left.2
      rw [hl, pairing_eq_iff]
      exact conj_pair_one e _ _ he hpair
    · rw [hl, conj_mE_right, h]
      exact iff_of_true he rfl
  · have hl : (mE e * x * (mE e)⁻¹).left = (x.left.1 * (dE e)⁻¹, dE e * x.left.2) := by
      rw [conj_mE_left, h, swapAut_gen]
      exact Prod.ext (by simp) (by simp)
    have he : x.left.1 ∉ a4Set := fun h' => C2Wreath.gen_ne_one (h ▸ hxp.mp h')
    refine ⟨?_, ?_⟩
    · show pairing (mE e * x * (mE e)⁻¹).left.1 = pairing (mE e * x * (mE e)⁻¹).left.2
      rw [hl, pairing_eq_iff]
      exact conj_pair_gen e _ _ he hpair
    · rw [hl, conj_mE_right, h]
      refine iff_of_false ?_ C2Wreath.gen_ne_one
      rw [a4_mul_iff]
      exact fun h' => he (h'.mpr (dE_even e).2)

/-- Conjugation by `mₑ` as an endomorphism of `Xg`. -/
def conjXg (e : Fin 3) : Xg →* Xg where
  toFun x := ⟨mE e * x * (mE e)⁻¹, conj_mE_mem e x x.2⟩
  map_one' := by
    apply Subtype.ext
    show mE e * 1 * (mE e)⁻¹ = 1
    group
  map_mul' x y := by
    apply Subtype.ext
    show mE e * ((x : W4) * y) * (mE e)⁻¹ =
      (mE e * x * (mE e)⁻¹) * (mE e * y * (mE e)⁻¹)
    group

theorem conjXg_injective (e : Fin 3) : Function.Injective (conjXg e) := by
  intro x y h
  have := congrArg Subtype.val h
  change mE e * (x : W4) * (mE e)⁻¹ = mE e * (y : W4) * (mE e)⁻¹ at this
  exact Subtype.ext (by simpa using this)

instance : Finite Xg := inferInstance

theorem conjXg_surjective (e : Fin 3) : Function.Surjective (conjXg e) :=
  Finite.surjective_of_injective (conjXg_injective e)

/-- The projection `Xg → S₄` with kernel `Δ_e`. -/
def projG (e : Fin 3) : Xg →* Perm (Fin 4) :=
  pi0.comp ((Subgroup.inclusion Xg_le_Xs).comp (conjXg e))

theorem section_mem_Xg (y : Perm (Fin 4)) :
    (inl (y, vOf (y 3) * y) * inr (if y ∈ a4Set then 1 else C2Wreath.gen) : W4) ∈ Xg := by
  refine ⟨section_mem_Xs y _, ?_⟩
  rw [section_left, mul_right, right_inl, one_mul, right_inr]
  by_cases hy : y ∈ a4Set
  · rw [if_pos hy]
    exact iff_of_true hy rfl
  · rw [if_neg hy]
    exact iff_of_false hy C2Wreath.gen_ne_one

theorem projG_surjective (e : Fin 3) : Function.Surjective (projG e) := by
  intro y
  obtain ⟨x, hx⟩ := conjXg_surjective e ⟨_, section_mem_Xg y⟩
  refine ⟨x, ?_⟩
  show pi0 (Subgroup.inclusion Xg_le_Xs (conjXg e x)) = y
  rw [hx]
  show pi0Fun (inl (y, vOf (y 3) * y) * inr _ : W4).left.1
    (inl (y, vOf (y 3) * y) * inr _ : W4).left.2 = y
  rw [section_left]
  exact (pi0_section y).2

/-- The kernel of `projG e` lies in `Δ_e`. -/
theorem projG_ker (e : Fin 3) (x : Xg) (hx : x ∈ (projG e).ker) :
    ∃ v ∈ kleinSet, (x : W4) = inl (v, (dE e)⁻¹ * v * dE e) := by
  have h0 : pi0Fun (mE e * (x : W4) * (mE e)⁻¹).left.1 (mE e * (x : W4) * (mE e)⁻¹).left.2 = 1 :=
    hx
  have hconjXs : mE e * (x : W4) * (mE e)⁻¹ ∈ Xs := Xg_le_Xs (conj_mE_mem e x x.2)
  have hpair := (pairing_eq_iff _ _).mp hconjXs
  obtain ⟨hk, heq⟩ := (pi0_ker_pair _ _ hpair).mp h0
  obtain ⟨_, hxp⟩ := x.2
  rcases C2Wreath.cases (x : W4).right with h | h
  · have hl : (mE e * (x : W4) * (mE e)⁻¹).left =
        ((x : W4).left.1, dE e * (x : W4).left.2 * (dE e)⁻¹) := by
      rw [conj_mE_left, h, swapAut_one]
      exact Prod.ext (by simp) (by simp)
    rw [hl] at hk heq
    refine ⟨(x : W4).left.1, hk, ?_⟩
    have hx2 : (x : W4).left.2 = (dE e)⁻¹ * (x : W4).left.1 * dE e := by
      simp only at heq
      rw [← heq]
      group
    calc (x : W4) = inl (x : W4).left := eq_inl_of_right _ h
      _ = inl ((x : W4).left.1, (dE e)⁻¹ * (x : W4).left.1 * dE e) := by
          congr 1
          exact Prod.ext rfl hx2
  · exfalso
    have hl : (mE e * (x : W4) * (mE e)⁻¹).left =
        ((x : W4).left.1 * (dE e)⁻¹, dE e * (x : W4).left.2) := by
      rw [conj_mE_left, h, swapAut_gen]
      exact Prod.ext (by simp) (by simp)
    rw [hl] at hk
    have heven : (x : W4).left.1 ∈ a4Set := by
      have h1 := kleinSet_sub_a4Set _ hk
      rw [a4_mul_iff] at h1
      exact h1.mpr (dE_even e).2
    exact C2Wreath.gen_ne_one (h ▸ hxp.mp heven)

/-- Every nontrivial normal subgroup contains one `Δ_e`, hence one kernel. -/
theorem projG_normal_cover (N : Subgroup Xg) (hN : N.Normal) (hNb : N ≠ ⊥) :
    ∃ e : Fin 3, (projG e).ker ≤ N := by
  haveI := hN
  have hinf := inf_ne_bot_of_selfCentralizing (VX Xg) (VX_selfCentralizing Xg VW_le_Xg) N hNb
  obtain ⟨⟨w, hwN, hwV⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinf
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwV' : (w : W4) ∈ VW := hwV
  obtain ⟨hwr, hw1k, hw2k⟩ := hwV'
  have hwW : (w : W4) = inl (w : W4).left := eq_inl_of_right _ hwr
  have hσ : gT * gS ∈ Xg := gTgS_mem_Xg
  -- an element of `N` in the base with both coordinates nonzero
  have hboth : ∃ u1 ∈ kleinSet, ∃ u2 ∈ kleinSet, u1 ≠ 1 ∧ u2 ≠ 1 ∧
      ∃ hu : (inl (u1, u2) : W4) ∈ Xg, (⟨inl (u1, u2), hu⟩ : Xg) ∈ N := by
    by_cases h1 : (w : W4).left.1 = 1 <;> by_cases h2 : (w : W4).left.2 = 1
    · exfalso
      apply hw1'
      apply Subtype.ext
      rw [hwW, show (w : W4).left = 1 from Prod.ext h1 h2, map_one]
      rfl
    · -- `(1, w₂)`: multiply by its `τ s` conjugate
      have hs := N.mul_mem hwN (hN.conj_mem w hwN ⟨gT * gS, hσ⟩)
      have hk := tau_conj_mem _ hw2k
      refine ⟨_, hk, _, hw2k, fun h => h2 (tau_conj_one _ hw2k h), h2,
        VW_le_Xg ⟨rfl, hk, hw2k⟩, ?_⟩
      convert hs using 1
      apply Subtype.ext
      show inl (tauLoc * (w : W4).left.2 * tauLoc⁻¹, (w : W4).left.2) =
        (w : W4) * ((gT * gS) * (w : W4) * (gT * gS)⁻¹)
      rw [hwW, conj_gTgS, inl_mul_inl]
      congr 1
      refine Prod.ext ?_ ?_ <;> simp [h1]
    · have hs := N.mul_mem hwN (hN.conj_mem w hwN ⟨gT * gS, hσ⟩)
      have hk := tau_conj_mem _ hw1k
      refine ⟨_, hw1k, _, hk, h1, fun h => h1 (tau_conj_one _ hw1k h),
        VW_le_Xg ⟨rfl, hw1k, hk⟩, ?_⟩
      convert hs using 1
      apply Subtype.ext
      show inl ((w : W4).left.1, tauLoc * (w : W4).left.1 * tauLoc⁻¹) =
        (w : W4) * ((gT * gS) * (w : W4) * (gT * gS)⁻¹)
      rw [hwW, conj_gTgS, inl_mul_inl]
      congr 1
      refine Prod.ext ?_ ?_ <;> simp [h2]
    · exact ⟨_, hw1k, _, hw2k, h1, h2, by rw [← hwW]; exact w.2, by
        convert hwN using 1
        exact Subtype.ext hwW.symm⟩
  obtain ⟨u1, hu1, u2, hu2, hu1n, hu2n, huX, huN⟩ := hboth
  obtain ⟨e, he⟩ := c_rotates u1 hu1 hu1n u2 hu2 hu2n
  refine ⟨e, fun x hx => ?_⟩
  obtain ⟨v, hv, hxv⟩ := projG_ker e x hx
  by_cases hv1 : v = 1
  · have : x = 1 := by
      apply Subtype.ext
      rw [hxv, hv1]
      show inl (1, (dE e)⁻¹ * 1 * dE e) = (1 : W4)
      rw [mul_one, inv_mul_cancel]
      exact map_one _
    rw [this]
    exact N.one_mem
  obtain ⟨k, hk⟩ := t3_rotates u1 hu1 hu1n v hv hv1
  have hc := hN.conj_mem _ huN ⟨gA ^ (k : ℕ), Xg.pow_mem gA_mem_Xg _⟩
  convert hc using 1
  apply Subtype.ext
  show (x : W4) = gA ^ (k : ℕ) * inl (u1, u2) * (gA ^ (k : ℕ))⁻¹
  rw [hxv, gA_pow, conj_inl, tLoc_eq_t3]
  congr 1
  refine Prod.ext hk.symm ?_
  show (dE e)⁻¹ * v * dE e = t3 ^ (k : ℕ) * u2 * (t3 ^ (k : ℕ))⁻¹
  rw [he, t3_c_commute _ hu1, hk]

/-! ## Derived series and the target -/

theorem gA_mem_derived_Xg : (⟨gA, gA_mem_Xg⟩ : Xg) ∈ derivedSeries Xg 1 := by
  have heq : (⟨gA, gA_mem_Xg⟩ : Xg) = ⁅(⟨gA, gA_mem_Xg⟩ : Xg), ⟨gT * gS, gTgS_mem_Xg⟩⁆ ^ 2 := by
    apply Subtype.ext
    rw [show ((⁅(⟨gA, gA_mem_Xg⟩ : Xg), (⟨gT * gS, gTgS_mem_Xg⟩ : Xg)⁆ ^ 2 : Xg) : W4) =
        ⁅gA, gT * gS⁆ ^ 2 by simp [commutatorElement_def]]
    exact gA_eq_comm_sq (gT * gS) gTgS_inverts
  rw [heq]
  exact Subgroup.pow_mem _ (mem_derivedSeries_one _ _) _

theorem Xg_derived_two : derivedSeries Xg 2 = VX Xg := by
  apply le_antisymm
  · intro x hx
    have h := map_derivedSeries_le_derivedSeries
      (pairHom.comp (Subgroup.inclusion Xg_le_Xs)) 2 ⟨x, hx, rfl⟩
    rw [derivedSeries_S3_two] at h
    have h1 : pairing (x : W4).left.1 = 1 := (Subgroup.mem_bot).mp h
    have hk : (x : W4).left.1 ∈ kleinSet := by
      rw [← mem_klein, ← ker_pairing]
      exact h1
    have hr : (x : W4).right = 1 := x.2.2.mp (kleinSet_sub_a4Set _ hk)
    exact mem_VW_of_pair _ (Xg_le_Xs x.2) h1 hr
  · have h1 : VX Xg ≤ derivedSeries Xg 1 :=
      VX_le_derived Xg gA_mem_Xg VW_le_Xg 0 (by simp) (by simp)
    exact VX_le_derived Xg gA_mem_Xg VW_le_Xg 1 gA_mem_derived_Xg h1

/-- `Xg` is a binary cyclic-dual target on the common source `J''`. -/
def targetG : DerivedHead.DerivedCyclicTarget Xg (VX Xg) 1 2 where
  derived_eq := Xg_derived_two
  character := chiX Xg
  self_centralizing := VX_selfCentralizing Xg VW_le_Xg
  absorbing := VX_absorbing Xg gA_mem_Xg 1 gA_mem_derived_Xg Xg_derived_two
  separating := chiX_separating Xg gA_mem_Xg (gT * gS) gTgS_mem_Xg
    (fun v => tauLoc * v * tauLoc⁻¹) tau_conj_mem tau_conj_one conj_gTgS

end TwoFourDiagonal
end SymmetricSubgroupAsymptotics
