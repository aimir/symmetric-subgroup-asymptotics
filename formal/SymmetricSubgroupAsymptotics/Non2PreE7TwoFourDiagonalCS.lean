import SymmetricSubgroupAsymptotics.Non2PreE7TwoFourDiagonalHead

/-!
# The classes `Xc` and `Xs`

Both contain the block exchange `s`, so every nontrivial normal subgroup
contains the diagonal `Δ = {(v, v)}`: a nonzero base vector times its
`s`-conjugate is diagonal, and the rotations by `a` fill `Δ`.  The diagonal
projection and the block exchange map `Xc` onto `A₄ × C₂` and `Xs` onto
`S₄ × C₂` with kernel `Δ`.

`Xc' = V` and `Xs'' = V`, so both are binary cyclic-dual targets.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace TwoFourDiagonal

open Equiv NaturalS4 C2Wreath SemidirectProduct

/-! ## Finite facts -/

theorem pairing_comm_a4 : ∀ a ∈ a4Set, ∀ b ∈ a4Set, ∀ i : Fin 3,
    pairFun a (pairFun b i) = pairFun b (pairFun a i) := by decide +kernel

theorem t3_rotates : ∀ u ∈ kleinSet, u ≠ 1 → ∀ v ∈ kleinSet, v ≠ 1 →
    ∃ k : Fin 3, t3 ^ (k : ℕ) * u * (t3 ^ (k : ℕ))⁻¹ = v := by decide +kernel

theorem klein_sq_one : ∀ u ∈ kleinSet, ∀ w ∈ kleinSet, u * w = 1 → u = w := by decide

/-! ## The pairing of the first coordinate -/

/-- `x ↦ p(x₁)` on `Xs`. -/
def pairHom : Xs →* Perm (Fin 3) where
  toFun x := pairing (x : W4).left.1
  map_one' := map_one pairing
  map_mul' x y := by
    show pairing ((x : W4) * y).left.1 = pairing (x : W4).left.1 * pairing (y : W4).left.1
    rcases C2Wreath.cases (x : W4).right with h | h
    · rw [left_mul_of_one _ _ h, Prod.fst_mul, map_mul]
    · rw [left_mul_of_gen _ _ h, map_mul]
      have hy : pairing (y : W4).left.1 = pairing (y : W4).left.2 := y.2
      rw [hy]

theorem mem_VW_of_pair (x : W4) (hx : x ∈ Xs) (h1 : pairing x.left.1 = 1) (hr : x.right = 1) :
    x ∈ VW := by
  have hx2 : pairing x.left.2 = 1 := by
    have : pairing x.left.1 = pairing x.left.2 := hx
    rw [← this, h1]
  refine ⟨hr, ?_, ?_⟩
  · rw [← mem_klein, ← ker_pairing]
    exact h1
  · rw [← mem_klein, ← ker_pairing]
    exact hx2

/-! ## The diagonal is in every nontrivial normal subgroup -/

theorem inl_mem_X {X : Subgroup W4} (hV : VW ≤ X) {p : Perm (Fin 4) × Perm (Fin 4)}
    (h1 : p.1 ∈ kleinSet) (h2 : p.2 ∈ kleinSet) : (inl p : W4) ∈ X :=
  hV ⟨rfl, h1, h2⟩

theorem diag_mem (X : Subgroup W4) (hA : gA ∈ X) (hS : gS ∈ X) (hV : VW ≤ X)
    (N : Subgroup X) (hN : N.Normal) (hNb : N ≠ ⊥) (v : Perm (Fin 4)) (hv : v ∈ kleinSet) :
    (⟨inl (v, v), inl_mem_X hV hv hv⟩ : X) ∈ N := by
  haveI := hN
  have hinf := inf_ne_bot_of_selfCentralizing (VX X) (VX_selfCentralizing X hV) N hNb
  obtain ⟨⟨w, hwN, hwV⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinf
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwV' : (w : W4) ∈ VW := hwV
  obtain ⟨hwr, hw1k, hw2k⟩ := hwV'
  have hwW : (w : W4) = inl (w : W4).left := eq_inl_of_right _ hwr
  -- a nontrivial diagonal element of `N`
  have hu : ∃ u ∈ kleinSet, u ≠ 1 ∧ ∃ hu' : (inl (u, u) : W4) ∈ X, (⟨inl (u, u), hu'⟩ : X) ∈ N := by
    have hsw := N.mul_mem hwN (hN.conj_mem w hwN ⟨gS, hS⟩)
    have hcoe : ((w * (⟨gS, hS⟩ * w * (⟨gS, hS⟩ : X)⁻¹) : X) : W4) =
        inl ((w : W4).left.1 * (w : W4).left.2, (w : W4).left.1 * (w : W4).left.2) := by
      show (w : W4) * (gS * (w : W4) * gS⁻¹) = _
      rw [hwW, conj_gS, inl_mul_inl, left_inl]
      congr 1
      refine Prod.ext rfl ?_
      exact kleinSet_comm _ hw2k _ hw1k
    by_cases hu1 : (w : W4).left.1 * (w : W4).left.2 = 1
    · have he := klein_sq_one _ hw1k _ hw2k hu1
      refine ⟨(w : W4).left.1, hw1k, ?_, inl_mem_X hV hw1k hw1k, ?_⟩
      · intro h1
        apply hw1'
        apply Subtype.ext
        rw [hwW, show (w : W4).left = 1 from Prod.ext h1 (he ▸ h1), map_one]
        rfl
      · convert hwN using 1
        apply Subtype.ext
        show inl ((w : W4).left.1, (w : W4).left.1) = (w : W4)
        rw [hwW, left_inl]
        congr 1
        exact Prod.ext rfl he
    · have hk := kleinSet_mul _ _ hw1k hw2k
      refine ⟨_, hk, hu1, inl_mem_X hV hk hk, ?_⟩
      convert hsw using 1
      exact Subtype.ext hcoe.symm
  obtain ⟨u, huk, hu1, huX, huN⟩ := hu
  by_cases hv1 : v = 1
  · have : (⟨inl (v, v), inl_mem_X hV hv hv⟩ : X) = 1 := by
      apply Subtype.ext
      show inl (v, v) = (1 : W4)
      rw [hv1]
      exact map_one _
    rw [this]
    exact N.one_mem
  obtain ⟨k, hk⟩ := t3_rotates u huk hu1 v hv hv1
  have hc := hN.conj_mem _ huN ⟨gA ^ (k : ℕ), X.pow_mem hA _⟩
  convert hc using 1
  apply Subtype.ext
  show inl (v, v) = gA ^ (k : ℕ) * inl (u, u) * (gA ^ (k : ℕ))⁻¹
  rw [gA_pow, conj_inl, tLoc_eq_t3]
  congr 1
  exact Prod.ext hk.symm hk.symm

/-! ## The projections -/

/-- `Xs → S₄ × C₂`. -/
def projS : Xs →* Perm (Fin 4) × Multiplicative (ZMod 2) := pi0.prod (blockHom Xs)

theorem section_mem_Xs (y : Perm (Fin 4)) (g : Multiplicative (ZMod 2)) :
    (inl (y, vOf (y 3) * y) * inr g : W4) ∈ Xs := by
  apply mem_Xs_of_pair _ g
  rw [xsPairs, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (pi0_section y).1.symm⟩

theorem section_left (y : Perm (Fin 4)) (g : Multiplicative (ZMod 2)) :
    (inl (y, vOf (y 3) * y) * inr g : W4).left = (y, vOf (y 3) * y) := by
  rw [left_mul_of_one _ _ rfl]
  simp

theorem projS_surjective : Function.Surjective projS := by
  rintro ⟨y, g⟩
  refine ⟨⟨_, section_mem_Xs y g⟩, Prod.ext ?_ ?_⟩
  · show pi0Fun (inl (y, vOf (y 3) * y) * inr g : W4).left.1
      (inl (y, vOf (y 3) * y) * inr g : W4).left.2 = y
    rw [section_left]
    exact (pi0_section y).2
  · show (inl (y, vOf (y 3) * y) * inr g : W4).right = g
    simp

theorem ker_proj_diag (X : Subgroup W4) (hXs : X ≤ Xs) (x : X)
    (h0 : pi0Fun (x : W4).left.1 (x : W4).left.2 = 1) (hr : (x : W4).right = 1) :
    (x : W4).left.1 ∈ kleinSet ∧ (x : W4) = inl ((x : W4).left.1, (x : W4).left.1) := by
  have hpair : pairFun (x : W4).left.1 = pairFun (x : W4).left.2 :=
    (pairing_eq_iff _ _).mp (hXs x.2)
  obtain ⟨hk, he⟩ := (pi0_ker_pair _ _ hpair).mp h0
  refine ⟨hk, ?_⟩
  rw [eq_inl_of_right _ hr]
  congr 1
  exact Prod.ext rfl he

theorem projS_normal_cover (N : Subgroup Xs) (hN : N.Normal) (hNb : N ≠ ⊥) :
    projS.ker ≤ N := by
  intro x hx
  have h0 : pi0 x = 1 := congrArg Prod.fst hx
  have hr : (x : W4).right = 1 := congrArg Prod.snd hx
  obtain ⟨hk, he⟩ := ker_proj_diag Xs le_rfl x h0 hr
  have := diag_mem Xs gA_mem_Xs gS_mem_Xs VW_le_Xs N hN hNb _ hk
  convert this using 1
  exact Subtype.ext he

/-- `Xc → A₄ × C₂`. -/
def projC : Xc →* a4 × Multiplicative (ZMod 2) :=
  ((pi0.comp (Subgroup.inclusion Xc_le_Xs)).codRestrict a4 (fun x =>
    pi0_even_pair _ _ x.2.2 ((pairing_eq_iff _ _).mp x.2.1))).prod (blockHom Xc)

theorem projC_surjective : Function.Surjective projC := by
  rintro ⟨⟨y, hy⟩, g⟩
  have hmem : (inl (y, vOf (y 3) * y) * inr g : W4) ∈ Xc := by
    refine ⟨section_mem_Xs y g, ?_⟩
    rw [section_left]
    exact hy
  refine ⟨⟨_, hmem⟩, Prod.ext ?_ ?_⟩
  · apply Subtype.ext
    show pi0Fun (inl (y, vOf (y 3) * y) * inr g : W4).left.1
      (inl (y, vOf (y 3) * y) * inr g : W4).left.2 = y
    rw [section_left]
    exact (pi0_section y).2
  · show (inl (y, vOf (y 3) * y) * inr g : W4).right = g
    simp

theorem projC_normal_cover (N : Subgroup Xc) (hN : N.Normal) (hNb : N ≠ ⊥) :
    projC.ker ≤ N := by
  intro x hx
  have h0 : pi0Fun (x : W4).left.1 (x : W4).left.2 = 1 := congrArg Subtype.val (congrArg Prod.fst hx)
  have hr : (x : W4).right = 1 := congrArg Prod.snd hx
  obtain ⟨hk, he⟩ := ker_proj_diag Xc Xc_le_Xs x h0 hr
  have := diag_mem Xc gA_mem_Xc gS_mem_Xc VW_le_Xc N hN hNb _ hk
  convert this using 1
  exact Subtype.ext he

/-! ## Derived series -/

theorem derivedSeries_prod_two_bot :
    derivedSeries (Perm (Fin 3) × Multiplicative (ZMod 2)) 2 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 := map_derivedSeries_le_derivedSeries (MonoidHom.fst (Perm (Fin 3))
    (Multiplicative (ZMod 2))) 2 ⟨x, hx, rfl⟩
  have h2 := map_derivedSeries_le_derivedSeries (MonoidHom.snd (Perm (Fin 3))
    (Multiplicative (ZMod 2))) 2 ⟨x, hx, rfl⟩
  rw [derivedSeries_S3_two] at h1
  have hc : derivedSeries (Multiplicative (ZMod 2)) 2 = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : derivedSeries (Multiplicative (ZMod 2)) 1 = ⊥ := by
      rw [derivedSeries_one, commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm a b)]
      exact Subgroup.one_mem _
    have hmono := derivedSeries_antitone (Multiplicative (ZMod 2)) (show 1 ≤ 2 by omega) hy
    rw [this] at hmono
    exact hmono
  rw [hc] at h2
  exact Prod.ext ((Subgroup.mem_bot).mp h1) ((Subgroup.mem_bot).mp h2)

theorem Xs_derived_two : derivedSeries Xs 2 = VX Xs := by
  apply le_antisymm
  · intro x hx
    have h := map_derivedSeries_le_derivedSeries (pairHom.prod (blockHom Xs)) 2 ⟨x, hx, rfl⟩
    rw [derivedSeries_prod_two_bot] at h
    have h' := (Subgroup.mem_bot).mp h
    exact mem_VW_of_pair _ x.2 (congrArg Prod.fst h') (congrArg Prod.snd h')
  · have h1 : VX Xs ≤ derivedSeries Xs 1 :=
      VX_le_derived Xs gA_mem_Xs VW_le_Xs 0 (by simp) (by simp)
    have hA : (⟨gA, gA_mem_Xs⟩ : Xs) ∈ derivedSeries Xs 1 := by
      have heq : (⟨gA, gA_mem_Xs⟩ : Xs) = ⁅(⟨gA, gA_mem_Xs⟩ : Xs), ⟨gT, gT_mem_Xs⟩⁆ ^ 2 := by
        apply Subtype.ext
        rw [show ((⁅(⟨gA, gA_mem_Xs⟩ : Xs), (⟨gT, gT_mem_Xs⟩ : Xs)⁆ ^ 2 : Xs) : W4) =
            ⁅gA, gT⁆ ^ 2 by simp [commutatorElement_def]]
        exact gA_eq_comm_sq gT gT_inverts
      rw [heq]
      exact Subgroup.pow_mem _ (mem_derivedSeries_one _ _) _
    exact VX_le_derived Xs gA_mem_Xs VW_le_Xs 1 hA h1

theorem Xc_derived_one : derivedSeries Xc 1 = VX Xc := by
  apply le_antisymm
  · rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have hhom := map_commutatorElement ((pairHom.comp (Subgroup.inclusion Xc_le_Xs)).prod
      (blockHom Xc)) x y
    have hone : ⁅((pairHom.comp (Subgroup.inclusion Xc_le_Xs)).prod (blockHom Xc)) x,
        ((pairHom.comp (Subgroup.inclusion Xc_le_Xs)).prod (blockHom Xc)) y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      refine Prod.ext ?_ (mul_comm _ _)
      refine Equiv.ext fun i => ?_
      exact pairing_comm_a4 _ x.2.2 _ y.2.2 i
    rw [hone] at hhom
    exact mem_VW_of_pair _ (Xc_le_Xs (⁅x, y⁆ : Xc).2) (congrArg Prod.fst hhom)
      (congrArg Prod.snd hhom)
  · exact VX_le_derived Xc gA_mem_Xc VW_le_Xc 0 (by simp) (by simp)

/-! ## The cyclic-dual targets -/

/-- `Xc` is a binary cyclic-dual target on the common source `J'`. -/
def targetC : DerivedHead.DerivedCyclicTarget Xc (VX Xc) 0 2 where
  derived_eq := Xc_derived_one
  character := chiX Xc
  self_centralizing := VX_selfCentralizing Xc VW_le_Xc
  absorbing := VX_absorbing Xc gA_mem_Xc 0 (by simp) Xc_derived_one
  separating := chiX_separating Xc gA_mem_Xc gS gS_mem_Xc id (fun _ h => h) (fun _ _ h => h)
    (fun p => by rw [conj_gS]; rfl)

/-- `Xs` is a binary cyclic-dual target on the common source `J''`. -/
def targetS : DerivedHead.DerivedCyclicTarget Xs (VX Xs) 1 2 where
  derived_eq := Xs_derived_two
  character := chiX Xs
  self_centralizing := VX_selfCentralizing Xs VW_le_Xs
  absorbing := by
    have hA : (⟨gA, gA_mem_Xs⟩ : Xs) ∈ derivedSeries Xs 1 := by
      have heq : (⟨gA, gA_mem_Xs⟩ : Xs) = ⁅(⟨gA, gA_mem_Xs⟩ : Xs), ⟨gT, gT_mem_Xs⟩⁆ ^ 2 := by
        apply Subtype.ext
        rw [show ((⁅(⟨gA, gA_mem_Xs⟩ : Xs), (⟨gT, gT_mem_Xs⟩ : Xs)⁆ ^ 2 : Xs) : W4) =
            ⁅gA, gT⁆ ^ 2 by simp [commutatorElement_def]]
        exact gA_eq_comm_sq gT gT_inverts
      rw [heq]
      exact Subgroup.pow_mem _ (mem_derivedSeries_one _ _) _
    exact VX_absorbing Xs gA_mem_Xs 1 hA Xs_derived_two
  separating := chiX_separating Xs gA_mem_Xs gS gS_mem_Xs id (fun _ h => h) (fun _ _ h => h)
    (fun p => by rw [conj_gS]; rfl)

end TwoFourDiagonal
end SymmetricSubgroupAsymptotics
