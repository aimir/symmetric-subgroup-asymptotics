import SymmetricSubgroupAsymptotics.CanonicalLifts
import SymmetricSubgroupAsymptotics.ElementaryClassical
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness

/-!
# The finite full-projection deficit

A failed projection of a binary subspace lies in the pullback of a coordinate
hyperplane. A coordinate of dimension at most four supplies at most fifteen
nonzero functionals, and every pullback hyperplane contains exactly `G_(r-1)`
subspaces. The count concerns literal subspaces, before any orbit weighting.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

private instance binaryDual_finite (d : ℕ) :
    Finite ((Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
  Finite.of_injective (fun l : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 =>
    (l : (Fin d → ZMod 2) → ZMod 2)) DFunLike.coe_injective

private theorem card_subtype_le_sum_of_cover {α ι : Type*} [Finite α] [Fintype ι]
    (P : α → Prop) (Q : ι → α → Prop)
    (hcover : ∀ x, P x → ∃ i, Q i x) :
    Nat.card {x // P x} ≤ ∑ i, Nat.card {x // Q i x} := by
  classical
  let g : {x // P x} → Σ i, {x // Q i x} := fun x =>
    ⟨Classical.choose (hcover x.1 x.2), x.1, Classical.choose_spec (hcover x.1 x.2)⟩
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : Σ i, {x // Q i x} => z.2.1) h)
  calc
    _ ≤ Nat.card (Σ i, {x // Q i x}) := Nat.card_le_card_of_injective g hg
    _ = _ := Nat.card_sigma

/-- A binary hyperplane contains exactly as many subspaces as binary space
of dimension one less. -/
theorem binaryHyperplane_subspace_count {r : ℕ}
    (l : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hl : l ≠ 0) :
    Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) // U ≤ l.ker} =
      binarySubspaceCount (r - 1) := by
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hl
  have hdim' : Module.finrank (ZMod 2) l.ker = r - 1 := by
    simp only [Module.finrank_pi, Fintype.card_fin] at hdim
    omega
  let e := LinearEquiv.ofFinrankEq (R := ZMod 2) l.ker (Fin (r - 1) → ZMod 2)
    (by simpa using hdim')
  exact Nat.card_congr ((Submodule.mapIic l.ker).toEquiv.symm.trans
    (Submodule.orderIsoMapComap e).toEquiv)

/-- The nonzero binary coordinate functionals number exactly `2^d-1`. -/
theorem binary_nonzero_dual_count (d : ℕ) :
    Nat.card {l : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 // l ≠ 0} = 2 ^ d - 1 := by
  classical
  letI := Fintype.ofFinite ((Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hcard : Fintype.card ((Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2) = 2 ^ d := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2)]
    change Nat.card (ZMod 2) ^
      Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Fin d → ZMod 2)) = 2 ^ d
    rw [Subspace.dual_finrank_eq, Module.finrank_pi, Fintype.card_fin, Nat.card_zmod]
  simp [hcard]

private theorem comp_ne_zero_of_surjective {r d : ℕ}
    (f : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
    (hf : Function.Surjective f)
    (l : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hl : l ≠ 0) :
    l.comp f ≠ 0 := by
  intro h
  apply hl
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact congrArg (fun g : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2 => g x) h

/-- Exact union-bound coefficient for arbitrary finite binary coordinate
widths. Coordinates need not be independent or jointly surjective. -/
theorem binarySubspace_bad_projection_count {r : ℕ} {ι : Type*} [Fintype ι]
    (d : ι → ℕ)
    (f : ∀ i, (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2))
    (hf : ∀ i, Function.Surjective (f i)) :
    Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) //
      ∃ i, U.map (f i) ≠ ⊤} ≤
        (∑ i, (2 ^ d i - 1)) * binarySubspaceCount (r - 1) := by
  classical
  let J := Σ i, {l : (Fin (d i) → ZMod 2) →ₗ[ZMod 2] ZMod 2 // l ≠ 0}
  letI : Fintype J := Fintype.ofFinite J
  have hc : ∀ U : Submodule (ZMod 2) (Fin r → ZMod 2),
      (∃ i, U.map (f i) ≠ ⊤) → ∃ j : J, U ≤ (j.2.1.comp (f j.1)).ker := by
    intro U hU
    obtain ⟨i, hi⟩ := hU
    obtain ⟨l, hl, hUl⟩ := (U.map (f i)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hi)
    refine ⟨⟨i, l, hl⟩, ?_⟩
    rw [LinearMap.ker_comp]
    exact Submodule.map_le_iff_le_comap.mp hUl
  calc
    _ ≤ ∑ j : J, Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) //
        U ≤ (j.2.1.comp (f j.1)).ker} :=
      card_subtype_le_sum_of_cover _ _ hc
    _ = ∑ _j : J, binarySubspaceCount (r - 1) := by
      apply Finset.sum_congr rfl
      intro j _
      exact binaryHyperplane_subspace_count _
        (comp_ne_zero_of_surjective (f j.1) (hf j.1) j.2.1 j.2.2)
    _ = Nat.card J * binarySubspaceCount (r - 1) := by simp [Nat.card_eq_fintype_card]
    _ = _ := by
      congr 1
      rw [Nat.card_sigma]
      exact Finset.sum_congr rfl (fun i _ => binary_nonzero_dual_count (d i))

/-- At most `r` surjective coordinates, each of dimension at most four,
exclude at most `15 r G_(r-1)` literal binary subspaces. -/
theorem binarySubspace_bad_projection_count_le {r : ℕ} {ι : Type*} [Fintype ι]
    (d : ι → ℕ)
    (f : ∀ i, (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2))
    (hf : ∀ i, Function.Surjective (f i))
    (hd : ∀ i, d i ≤ 4) (hι : Fintype.card ι ≤ r) :
    Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) //
      ∃ i, U.map (f i) ≠ ⊤} ≤ 15 * r * binarySubspaceCount (r - 1) := by
  apply (binarySubspace_bad_projection_count d f hf).trans
  apply Nat.mul_le_mul_right
  calc
    ∑ i, (2 ^ d i - 1) ≤ ∑ _i : ι, 15 := by
      apply Finset.sum_le_sum
      intro i _
      have hpow : 2 ^ d i ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (hd i)
      omega
    _ = 15 * Fintype.card ι := by simp [Nat.mul_comm]
    _ ≤ 15 * r := Nat.mul_le_mul_left 15 hι

/-- The same estimate as a deficit from the complete subspace count. -/
theorem binarySubspace_full_projection_deficit {r : ℕ} {ι : Type*} [Fintype ι]
    (d : ι → ℕ)
    (f : ∀ i, (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2))
    (hf : ∀ i, Function.Surjective (f i))
    (hd : ∀ i, d i ≤ 4) (hι : Fintype.card ι ≤ r) :
    binarySubspaceCount r -
      Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) // ∀ i, U.map (f i) = ⊤} ≤
        15 * r * binarySubspaceCount (r - 1) := by
  classical
  letI := Fintype.ofFinite (Submodule (ZMod 2) (Fin r → ZMod 2))
  have hbad : Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) //
      ∃ i, U.map (f i) ≠ ⊤} = binarySubspaceCount r -
        Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) // ∀ i, U.map (f i) = ⊤} := by
    calc
      _ = Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) //
          ¬ ∀ i, U.map (f i) = ⊤} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun U => by simp)
      _ = _ := by
        simp only [binarySubspaceCount, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [← hbad]
  exact binarySubspace_bad_projection_count_le d f hf hd hι

/-- Passing from a binary linear map to its multiplicative group map
preserves the literal full-projection condition. -/
theorem binaryLinearMap_full_projection_iff {r d : ℕ}
    (f : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
    (U : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    U.toAddSubgroup.toSubgroup.map (AddMonoidHom.toMultiplicative f.toAddMonoidHom) = ⊤ ↔
      U.map f = ⊤ := by
  have hmap : U.toAddSubgroup.toSubgroup.map
      (AddMonoidHom.toMultiplicative f.toAddMonoidHom) =
      binarySubmoduleSubgroupOrderIso d (U.map f) := by
    ext x
    rfl
  rw [hmap, ← (binarySubmoduleSubgroupOrderIso d).map_top]
  exact (binarySubmoduleSubgroupOrderIso d).injective.eq_iff

/-- The hyperplane count applies to actual canonical subgroups and actual
factor projections, through explicit commuting squares and retained kernels.
There is no Frattini assumption and no identification modulo conjugacy. -/
theorem canonicalLift_bad_projection_count_le {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π)
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (D : ι → Type*) [∀ i, Group (D i)]
    (p : ∀ i, G →* D i)
    (q : ∀ i, D i →* Multiplicative (Fin (d i) → ZMod 2))
    (hq : ∀ i, Function.Surjective (q i))
    (f : ∀ i, (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2))
    (hf : ∀ i, Function.Surjective (f i))
    (hcomm : ∀ i, (q i).comp (p i) =
      (AddMonoidHom.toMultiplicative (f i).toAddMonoidHom).comp π)
    (hker : ∀ i, (q i).ker ≤ π.ker.map (p i))
    (hd : ∀ i, d i ≤ 4) (hι : Fintype.card ι ≤ r) :
    Nat.card {H : Subgroup G // π.ker ≤ H ∧ ∃ i, H.map (p i) ≠ ⊤} ≤
      15 * r * binarySubspaceCount (r - 1) := by
  calc
    _ = Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) //
        ∃ i, (canonicalLift π U).map (p i) ≠ ⊤} :=
      (Nat.card_congr (canonicalLiftFilterEquiv π hπ
        (fun H => ∃ i, H.map (p i) ≠ ⊤))).symm
    _ = Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) //
        ∃ i, U.map (f i) ≠ ⊤} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro U
      apply exists_congr
      intro i
      exact not_congr ((canonicalLift_full_projection_iff π hπ (p i) (q i) (hq i)
        (AddMonoidHom.toMultiplicative (f i).toAddMonoidHom) (hcomm i) (hker i) U).trans
          (binaryLinearMap_full_projection_iff (f i) U))
    _ ≤ _ := binarySubspace_bad_projection_count_le d f hf hd hι

/-- The full-projecting canonical family loses at most `15 r G_(r-1)`
from its exact all-subspace count. -/
theorem canonicalLift_full_projection_deficit {G : Type*} [Group G] {r : ℕ}
    (π : G →* Multiplicative (Fin r → ZMod 2)) (hπ : Function.Surjective π)
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (D : ι → Type*) [∀ i, Group (D i)]
    (p : ∀ i, G →* D i)
    (q : ∀ i, D i →* Multiplicative (Fin (d i) → ZMod 2))
    (hq : ∀ i, Function.Surjective (q i))
    (f : ∀ i, (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2))
    (hf : ∀ i, Function.Surjective (f i))
    (hcomm : ∀ i, (q i).comp (p i) =
      (AddMonoidHom.toMultiplicative (f i).toAddMonoidHom).comp π)
    (hker : ∀ i, (q i).ker ≤ π.ker.map (p i))
    (hd : ∀ i, d i ≤ 4) (hι : Fintype.card ι ≤ r) :
    binarySubspaceCount r -
      Nat.card {H : Subgroup G // π.ker ≤ H ∧ ∀ i, H.map (p i) = ⊤} ≤
        15 * r * binarySubspaceCount (r - 1) := by
  rw [canonicalLift_full_count π hπ D (fun i => Multiplicative (Fin (d i) → ZMod 2))
    p q hq (fun i => AddMonoidHom.toMultiplicative (f i).toAddMonoidHom) hcomm hker]
  have he : Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) // ∀ i,
      U.toAddSubgroup.toSubgroup.map (AddMonoidHom.toMultiplicative (f i).toAddMonoidHom) = ⊤} =
      Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) // ∀ i, U.map (f i) = ⊤} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun U =>
      forall_congr' fun i => binaryLinearMap_full_projection_iff (f i) U)
  rw [he]
  exact binarySubspace_full_projection_deficit d f hf hd hι

/-- The maximal Gaussian exponent gains `floor((r+1)/2)` at rank `r+1`. -/
theorem gaussianPower_succ (r : ℕ) :
    gaussianPower (r + 1) = gaussianPower r + (r + 1) / 2 := by
  have hcases : (∃ m, r = 2 * m) ∨ ∃ m, r = 2 * m + 1 := by
    by_cases he : r % 2 = 0
    · exact Or.inl ⟨r / 2, by omega⟩
    · exact Or.inr ⟨r / 2, by omega⟩
  rcases hcases with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [gaussianPower_odd, gaussianPower_even, show (2 * m + 1) / 2 = m by omega]
    ring
  · rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
      gaussianPower_even, gaussianPower_odd, show 2 * (m + 1) / 2 = m + 1 by omega]
    ring

/-- Uniform adjacent-rank Gaussian decay, on the full `2^(-r/2)` scale.
The constant and threshold are independent of all coordinate profiles. -/
theorem binarySubspaceCount_predecessor_ratio :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ r ≥ N,
      (binarySubspaceCount (r - 1) : ℝ) / binarySubspaceCount r ≤
        C * (2 : ℝ) ^ (-(r : ℝ) / 2) := by
  obtain ⟨N, hN, hbound⟩ := binaryGaussianSum_log_error
  let B : ℝ := 2 + Real.log (max kappaEven kappaOdd) -
    Real.log (min kappaEven kappaOdd) + Real.log 2
  refine ⟨Real.exp B, Real.exp_pos _, N + 1, by omega, ?_⟩
  intro r hr
  have hr2 : 2 ≤ r := by omega
  have hrm2 : 2 ≤ r - 1 := by omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrmpos : (0 : ℝ) < (r - 1 : ℕ) := by exact_mod_cast (show 0 < r - 1 by omega)
  have hcast (s : ℕ) : (binaryGaussianSum s : ℝ) = (binarySubspaceCount s : ℝ) := by
    exact_mod_cast (binarySubspaceCount_eq_gaussianSum s).symm
  have hu := hbound (r - 1) (by omega)
  have hl := hbound r (by omega)
  rw [hcast] at hu hl
  have hu1 : 2 / ((r - 1 : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hrmpos).mpr
    norm_num
    exact_mod_cast hrm2
  have hl1 : 2 / (r : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hrpos).mpr
    norm_num
    exact_mod_cast hr2
  have hku : Real.log (gaussianKappa (r - 1)) ≤ Real.log (max kappaEven kappaOdd) := by
    apply Real.log_le_log (gaussianKappa_pos _)
    unfold gaussianKappa
    split_ifs <;> simp only [le_max_left, le_max_right]
  have hkl : Real.log (min kappaEven kappaOdd) ≤ Real.log (gaussianKappa r) := by
    apply Real.log_le_log (lt_min kappaEven_pos kappaOdd_pos)
    unfold gaussianKappa
    split_ifs <;> simp only [min_le_left, min_le_right]
  have hpow : gaussianPower r = gaussianPower (r - 1) + r / 2 := by
    simpa [Nat.sub_add_cancel (show 1 ≤ r by omega)] using gaussianPower_succ (r - 1)
  have hpowR : (gaussianPower r : ℝ) =
      (gaussianPower (r - 1) : ℝ) + (r / 2 : ℕ) := by exact_mod_cast hpow
  have hfloor : (r : ℝ) / 2 - 1 ≤ (r / 2 : ℕ) := by
    have h : r ≤ 2 * (r / 2) + 1 := by omega
    have h' : (r : ℝ) ≤ 2 * (r / 2 : ℕ) + 1 := by exact_mod_cast h
    linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log (binarySubspaceCount (r - 1) : ℝ) -
      Real.log (binarySubspaceCount r : ℝ) ≤ B + (-(r : ℝ) / 2) * Real.log 2 := by
    have hu' := (abs_le.mp hu).2
    have hl' := (abs_le.mp hl).1
    have hfloor' := mul_le_mul_of_nonneg_right hfloor hlog2
    dsimp [B]
    nlinarith
  have hGm : (0 : ℝ) < binarySubspaceCount (r - 1) := by
    exact_mod_cast binarySubspaceCount_pos (r - 1)
  have hG : (0 : ℝ) < binarySubspaceCount r := by
    exact_mod_cast binarySubspaceCount_pos r
  calc
    _ = Real.exp (Real.log (binarySubspaceCount (r - 1) : ℝ) -
        Real.log (binarySubspaceCount r : ℝ)) := by
      rw [Real.exp_sub, Real.exp_log hGm, Real.exp_log hG]
    _ ≤ Real.exp (B + (-(r : ℝ) / 2) * Real.log 2) := Real.exp_le_exp.mpr hlog
    _ = _ := by rw [Real.exp_add, Real.rpow_def_of_pos (by norm_num)]; congr 2; ring

/-- A uniform relative deficit for every eligible coordinate profile.
The profile, its maps and its coordinate count may all vary with the rank. -/
theorem binarySubspace_full_projection_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ r ≥ N,
      ∀ {ι : Type*} [Fintype ι] (d : ι → ℕ)
        (f : ∀ i, (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2)),
      (∀ i, Function.Surjective (f i)) → (∀ i, d i ≤ 4) → Fintype.card ι ≤ r →
      |(Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) //
          ∀ i, U.map (f i) = ⊤} : ℝ) / binarySubspaceCount r - 1| ≤
        C * r * (2 : ℝ) ^ (-(r : ℝ) / 2) := by
  obtain ⟨C, hC, N, hN, hratio⟩ := binarySubspaceCount_predecessor_ratio
  refine ⟨15 * C, by positivity, N, hN, ?_⟩
  intro r hr ι _ d f hf hd hι
  let A := Nat.card {U : Submodule (ZMod 2) (Fin r → ZMod 2) // ∀ i, U.map (f i) = ⊤}
  have hA : A ≤ binarySubspaceCount r :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hdef := binarySubspace_full_projection_deficit d f hf hd hι
  have hG : (0 : ℝ) < binarySubspaceCount r := by exact_mod_cast binarySubspaceCount_pos r
  have hdefR : (binarySubspaceCount r : ℝ) - A ≤
      15 * r * (binarySubspaceCount (r - 1) : ℝ) := by
    exact_mod_cast hdef
  have hAr : (A : ℝ) ≤ binarySubspaceCount r := by exact_mod_cast hA
  have habs : |(A : ℝ) / binarySubspaceCount r - 1| =
      ((binarySubspaceCount r : ℝ) - A) / binarySubspaceCount r := by
    rw [abs_of_nonpos (by exact (div_le_one hG).mpr hAr |> sub_nonpos.mpr)]
    field_simp
    ring
  change |(A : ℝ) / binarySubspaceCount r - 1| ≤ _
  rw [habs]
  calc
    _ ≤ (15 * r * (binarySubspaceCount (r - 1) : ℝ)) / binarySubspaceCount r :=
      div_le_div_of_nonneg_right hdefR hG.le
    _ = (15 * r) * ((binarySubspaceCount (r - 1) : ℝ) / binarySubspaceCount r) := by ring
    _ ≤ (15 * r) * (C * (2 : ℝ) ^ (-(r : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (hratio r hr) (by positivity)
    _ = _ := by ring

/-- Uniform relative full-projection count for actual canonical subgroups.
The constants precede every profile, group, quotient and action map. -/
theorem canonicalLift_full_projection_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ r ≥ N,
      ∀ {G : Type*} [Group G]
        (π : G →* Multiplicative (Fin r → ZMod 2)), Function.Surjective π →
      ∀ {ι : Type*} [Fintype ι] (d : ι → ℕ) (D : ι → Type*) [∀ i, Group (D i)]
        (p : ∀ i, G →* D i)
        (q : ∀ i, D i →* Multiplicative (Fin (d i) → ZMod 2)),
      (∀ i, Function.Surjective (q i)) →
      ∀ (f : ∀ i, (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2)),
      (∀ i, Function.Surjective (f i)) →
      (∀ i, (q i).comp (p i) =
        (AddMonoidHom.toMultiplicative (f i).toAddMonoidHom).comp π) →
      (∀ i, (q i).ker ≤ π.ker.map (p i)) →
      (∀ i, d i ≤ 4) → Fintype.card ι ≤ r →
      |(Nat.card {H : Subgroup G // π.ker ≤ H ∧ ∀ i, H.map (p i) = ⊤} : ℝ) /
          binarySubspaceCount r - 1| ≤ C * r * (2 : ℝ) ^ (-(r : ℝ) / 2) := by
  obtain ⟨C, hC, N, hN, hbound⟩ := binarySubspace_full_projection_relative_error
  refine ⟨C, hC, N, hN, ?_⟩
  intro r hr G _ π hπ ι _ d D _ p q hq f hf hcomm hker hd hι
  have hcount := canonicalLift_full_count π hπ D
    (fun i => Multiplicative (Fin (d i) → ZMod 2)) p q hq
    (fun i => AddMonoidHom.toMultiplicative (f i).toAddMonoidHom) hcomm hker
  simp_rw [binaryLinearMap_full_projection_iff] at hcount
  rw [hcount]
  exact hbound r hr d f hf hd hι

end SymmetricSubgroupAsymptotics
