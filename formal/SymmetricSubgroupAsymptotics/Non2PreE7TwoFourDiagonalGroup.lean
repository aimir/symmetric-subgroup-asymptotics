import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath
import SymmetricSubgroupAsymptotics.Non2PreE7A4WreathC2Group

/-!
# The three named diagonal classes `Xc`, `Xg`, `Xs` of TF

Inside `S₄ ≀ C₂`, acting on two blocks of four points, put

* `a = (t, t)` with `t = (0 1 2)` in both blocks (`(123)(567)`),
* `τ = (τ₀, τ₀)` with `τ₀ = (0 1)` in both blocks (`(12)(56)`),
* `s` the block exchange (`(15)(26)(37)(48)`),
* `V = V₄ × V₄` the two local Klein groups.

The named classes are `Xc = ⟨V, a, s⟩`, `Xg = ⟨V, a, τ s⟩` and
`Xs = ⟨V, a, τ, s⟩`.  This file identifies them with the literal subgroups

* `Xs = {(x₁, x₂; g) : x₁ ≡ x₂ mod V₄}`,
* `Xc = {(x₁, x₂; g) ∈ Xs : x₁ even}`,
* `Xg = {(x₁, x₂; g) ∈ Xs : x₁ even ↔ g = 1}`,

of orders `192, 96, 96`.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace TwoFourDiagonal

open Equiv NaturalS4 C2Wreath SemidirectProduct

/-- `S₄ ≀ C₂`. -/
abbrev W4 := C2Wreath.W (Perm (Fin 4))

instance : Finite W4 := Finite.of_equiv _ SemidirectProduct.equivProd.symm

/-- The natural action on the two blocks. -/
def natural : W4 →* Perm (Fin 4 ⊕ Fin 4) := C2Wreath.action (MonoidHom.id _)

theorem natural_injective : Function.Injective natural :=
  C2Wreath.action_injective _ Function.injective_id

/-! ## Componentwise multiplication -/

theorem left_mul_of_one (x y : W4) (hx : x.right = 1) : (x * y).left = x.left * y.left := by
  rw [mul_left', hx, swapAut_one]

theorem left_mul_of_gen (x y : W4) (hx : x.right = C2Wreath.gen) :
    (x * y).left = (x.left.1 * y.left.2, x.left.2 * y.left.1) := by
  rw [mul_left', hx, swapAut_gen]
  rfl

theorem left_inv_of_one (x : W4) (hx : x.right = 1) : (x⁻¹).left = x.left⁻¹ := by
  rw [inv_left, hx, inv_one, swapAut_one]

theorem left_inv_of_gen (x : W4) (hx : x.right = C2Wreath.gen) :
    (x⁻¹).left = (x.left.2⁻¹, x.left.1⁻¹) := by
  rw [inv_left, hx, C2Wreath.gen_inv, swapAut_gen]
  rfl

/-! ## Finite facts on `S₄` and `C₂` -/

theorem a4_mul_iff : ∀ x y : Perm (Fin 4), x * y ∈ a4Set ↔ (x ∈ a4Set ↔ y ∈ a4Set) := by
  decide +kernel

theorem a4_inv_iff : ∀ x : Perm (Fin 4), x⁻¹ ∈ a4Set ↔ x ∈ a4Set := by decide

theorem a4_of_pairing : ∀ x y : Perm (Fin 4), pairFun x = pairFun y →
    (x ∈ a4Set ↔ y ∈ a4Set) := by decide +kernel

theorem c2_mul_iff : ∀ u v : Multiplicative (ZMod 2), u * v = 1 ↔ (u = 1 ↔ v = 1) := by decide

theorem c2_inv : ∀ u : Multiplicative (ZMod 2), u⁻¹ = u := by decide

theorem pairing_eq_iff (x y : Perm (Fin 4)) : pairing x = pairing y ↔ pairFun x = pairFun y := by
  constructor
  · intro h
    funext i
    exact congrArg (fun σ : Perm (Fin 3) => σ i) h
  · intro h
    ext i
    simp [pairing_apply, h]

/-! ## The three literal subgroups -/

/-- `Xs`: the two local components agree modulo `V₄`. -/
def Xs : Subgroup W4 where
  carrier := {x | pairing x.left.1 = pairing x.left.2}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    show pairing (x * y).left.1 = pairing (x * y).left.2
    rcases C2Wreath.cases x.right with h | h
    · rw [left_mul_of_one x y h]
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
      rw [show pairing x.left.1 = pairing x.left.2 from hx,
        show pairing y.left.1 = pairing y.left.2 from hy]
    · rw [left_mul_of_gen x y h]
      simp only [map_mul]
      rw [show pairing x.left.1 = pairing x.left.2 from hx,
        show pairing y.left.1 = pairing y.left.2 from hy]
  inv_mem' := by
    intro x hx
    show pairing (x⁻¹).left.1 = pairing (x⁻¹).left.2
    rcases C2Wreath.cases x.right with h | h
    · rw [left_inv_of_one x h]
      simp only [Prod.fst_inv, Prod.snd_inv, map_inv]
      rw [show pairing x.left.1 = pairing x.left.2 from hx]
    · rw [left_inv_of_gen x h]
      simp only [map_inv]
      rw [show pairing x.left.1 = pairing x.left.2 from hx]

theorem mem_Xs (x : W4) : x ∈ Xs ↔ pairing x.left.1 = pairing x.left.2 := Iff.rfl

theorem a4_second_iff {x : W4} (hx : x ∈ Xs) : (x.left.2 ∈ a4Set ↔ x.left.1 ∈ a4Set) :=
  (a4_of_pairing _ _ ((pairing_eq_iff _ _).mp hx)).symm

/-- `Xc`: both local components even. -/
def Xc : Subgroup W4 where
  carrier := {x | x ∈ Xs ∧ x.left.1 ∈ a4Set}
  one_mem' := ⟨Xs.one_mem, by decide⟩
  mul_mem' := by
    rintro x y ⟨hx, hx4⟩ ⟨hy, hy4⟩
    refine ⟨Xs.mul_mem hx hy, ?_⟩
    rcases C2Wreath.cases x.right with h | h
    · rw [left_mul_of_one x y h]
      exact (a4_mul_iff _ _).mpr (iff_of_true hx4 hy4)
    · rw [left_mul_of_gen x y h]
      exact (a4_mul_iff _ _).mpr (iff_of_true hx4 ((a4_second_iff hy).mpr hy4))
  inv_mem' := by
    rintro x ⟨hx, hx4⟩
    refine ⟨Xs.inv_mem hx, ?_⟩
    rcases C2Wreath.cases x.right with h | h
    · rw [left_inv_of_one x h]
      exact (a4_inv_iff _).mpr hx4
    · rw [left_inv_of_gen x h]
      exact (a4_inv_iff _).mpr ((a4_second_iff hx).mpr hx4)

/-- `Xg`: the local parity is the block exchange. -/
def Xg : Subgroup W4 where
  carrier := {x | x ∈ Xs ∧ (x.left.1 ∈ a4Set ↔ x.right = 1)}
  one_mem' := ⟨Xs.one_mem, by decide⟩
  mul_mem' := by
    rintro x y ⟨hx, hxp⟩ ⟨hy, hyp⟩
    refine ⟨Xs.mul_mem hx hy, ?_⟩
    rw [mul_right, c2_mul_iff]
    rcases C2Wreath.cases x.right with h | h
    · rw [left_mul_of_one x y h, Prod.fst_mul, a4_mul_iff, hxp, hyp]
    · rw [left_mul_of_gen x y h, a4_mul_iff, hxp, (a4_second_iff hy), hyp]
  inv_mem' := by
    rintro x ⟨hx, hxp⟩
    refine ⟨Xs.inv_mem hx, ?_⟩
    rw [inv_right, c2_inv]
    rcases C2Wreath.cases x.right with h | h
    · rw [left_inv_of_one x h, Prod.fst_inv, a4_inv_iff, hxp]
    · rw [left_inv_of_gen x h, a4_inv_iff, (a4_second_iff hx), hxp]

theorem Xc_le_Xs : Xc ≤ Xs := fun _ hx => hx.1

theorem Xg_le_Xs : Xg ≤ Xs := fun _ hx => hx.1

/-! ## The named generators -/

/-- The local three-cycle `t = (0 1 2)`. -/
def tLoc : Perm (Fin 4) := swap 0 1 * swap 1 2

/-- The local transposition `τ₀ = (0 1)`. -/
def tauLoc : Perm (Fin 4) := swap 0 1

/-- `a = (123)(567)`. -/
def gA : W4 := inl (tLoc, tLoc)

/-- `τ = (12)(56)`. -/
def gT : W4 := inl (tauLoc, tauLoc)

/-- `s = (15)(26)(37)(48)`. -/
def gS : W4 := inr C2Wreath.gen

/-- The literal base `V₄ × V₄`. -/
def baseSet : Set W4 := {x | x.right = 1 ∧ x.left.1 ∈ kleinSet ∧ x.left.2 ∈ kleinSet}

/-- The generators `V₄², a, s` of `Xc`. -/
def XcGens : Set W4 := baseSet ∪ {gA, gS}

/-- The generators `V₄², a, τ s` of `Xg`. -/
def XgGens : Set W4 := baseSet ∪ {gA, gT * gS}

/-- The generators `V₄², a, τ, s` of `Xs`. -/
def XsGens : Set W4 := baseSet ∪ {gA, gT, gS}

theorem decompose_even : ∀ x1 x2 : Perm (Fin 4), x1 ∈ a4Set → pairFun x1 = pairFun x2 →
    ∃ v1 ∈ kleinSet, ∃ v2 ∈ kleinSet, ∃ k : Fin 3,
      x1 = v1 * tLoc ^ (k : ℕ) ∧ x2 = v2 * tLoc ^ (k : ℕ) := by decide +kernel

theorem decompose_all : ∀ x1 x2 : Perm (Fin 4), pairFun x1 = pairFun x2 →
    ∃ v1 ∈ kleinSet, ∃ v2 ∈ kleinSet, ∃ k : Fin 3, ∃ j : Fin 2,
      x1 = v1 * tLoc ^ (k : ℕ) * tauLoc ^ (j : ℕ) ∧
        x2 = v2 * tLoc ^ (k : ℕ) * tauLoc ^ (j : ℕ) := by decide +kernel

theorem tauLoc_pow_mem_iff : ∀ v ∈ kleinSet, ∀ k : Fin 3, ∀ j : Fin 2,
    (v * tLoc ^ (k : ℕ) * tauLoc ^ (j : ℕ) ∈ a4Set ↔ (j : ℕ) = 0) := by decide +kernel

theorem inl_mem_closure_base {S : Set W4} (hS : baseSet ⊆ S) (v1 v2 : Perm (Fin 4))
    (h1 : v1 ∈ kleinSet) (h2 : v2 ∈ kleinSet) :
    (inl (v1, v2) : W4) ∈ Subgroup.closure S :=
  Subgroup.subset_closure (hS ⟨rfl, h1, h2⟩)

theorem inl_pow (p : Perm (Fin 4) × Perm (Fin 4)) (n : ℕ) :
    (inl p : W4) ^ n = inl (p ^ n) := (map_pow _ p n).symm

theorem Xc_eq_closure : Xc = Subgroup.closure XcGens := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxs, hx4⟩ := hx
    obtain ⟨v1, hv1, v2, hv2, k, e1, e2⟩ :=
      decompose_even _ _ hx4 ((pairing_eq_iff _ _).mp hxs)
    have hx' : x = inl (v1, v2) * gA ^ (k : ℕ) * inr x.right := by
      conv_lhs => rw [← inl_left_mul_inr_right x]
      rw [gA, inl_pow, ← map_mul]
      congr 2
      refine Prod.ext ?_ ?_
      · simp [e1]
      · simp [e2]
    rw [hx']
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _
      (inl_mem_closure_base Set.subset_union_left _ _ hv1 hv2)
      (Subgroup.pow_mem _ (Subgroup.subset_closure
        (show gA ∈ XcGens from Or.inr (Or.inl rfl))) _)) ?_
    rcases C2Wreath.cases x.right with h | h
    · rw [h, map_one]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.subset_closure (show gS ∈ XcGens from Or.inr (Or.inr rfl))
  · rw [Subgroup.closure_le]
    rintro x (⟨hr, h1, h2⟩ | hx | hx)
    · refine ⟨?_, kleinSet_sub_a4Set _ h1⟩
      show pairing x.left.1 = pairing x.left.2
      have e1 : pairing x.left.1 = 1 := by
        rw [← MonoidHom.mem_ker, ker_pairing]
        exact h1
      have e2 : pairing x.left.2 = 1 := by
        rw [← MonoidHom.mem_ker, ker_pairing]
        exact h2
      rw [e1, e2]
    · rw [hx]
      exact ⟨rfl, by decide⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨rfl, by decide⟩

theorem decompose_eq (x : W4) (v1 v2 : Perm (Fin 4)) (k : Fin 3) (j : Fin 2)
    (e1 : x.left.1 = v1 * tLoc ^ (k : ℕ) * tauLoc ^ (j : ℕ))
    (e2 : x.left.2 = v2 * tLoc ^ (k : ℕ) * tauLoc ^ (j : ℕ)) :
    x = inl (v1, v2) * gA ^ (k : ℕ) * gT ^ (j : ℕ) * inr x.right := by
  conv_lhs => rw [← inl_left_mul_inr_right x]
  rw [gA, gT, inl_pow, inl_pow, ← map_mul, ← map_mul]
  congr 2
  refine Prod.ext ?_ ?_
  · simp [e1]
  · simp [e2]

theorem mem_closure_of_decompose {S : Set W4} (hS : baseSet ⊆ S) (hA : gA ∈ S)
    (x : W4) (v1 v2 : Perm (Fin 4)) (hv1 : v1 ∈ kleinSet) (hv2 : v2 ∈ kleinSet) (k : Fin 3)
    (rest : W4) (hrest : rest ∈ Subgroup.closure S) :
    inl (v1, v2) * gA ^ (k : ℕ) * rest ∈ Subgroup.closure S :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (inl_mem_closure_base hS _ _ hv1 hv2)
    (Subgroup.pow_mem _ (Subgroup.subset_closure hA) _)) hrest

theorem gT_gS_left : (gT * gS).left = (tauLoc, tauLoc) := by
  rw [left_mul_of_one gT gS rfl]
  rfl

theorem Xg_eq_closure : Xg = Subgroup.closure XgGens := by
  apply le_antisymm
  · rintro x ⟨hxs, hxp⟩
    obtain ⟨v1, hv1, v2, hv2, k, j, e1, e2⟩ := decompose_all _ _ ((pairing_eq_iff _ _).mp hxs)
    have hpar := tauLoc_pow_mem_iff v1 hv1 k j
    rw [← e1, hxp] at hpar
    rw [decompose_eq x v1 v2 k j e1 e2, mul_assoc _ (gT ^ (j : ℕ))]
    apply mem_closure_of_decompose Set.subset_union_left (Or.inr (Or.inl rfl)) x v1 v2 hv1 hv2
    fin_cases j
    · have hr : x.right = 1 := hpar.mpr rfl
      simp [hr]
    · have hr : x.right ≠ 1 := fun h => absurd (hpar.mp h) (by decide)
      have hr' : x.right = C2Wreath.gen := (C2Wreath.cases _).resolve_left hr
      simp only [pow_one]
      rw [hr', ← gS]
      exact Subgroup.subset_closure (show gT * gS ∈ XgGens from Or.inr (Or.inr rfl))
  · rw [Subgroup.closure_le]
    rintro x (⟨hr, h1, h2⟩ | hx | hx)
    · refine ⟨?_, ?_⟩
      · show pairing x.left.1 = pairing x.left.2
        have e1 : pairing x.left.1 = 1 := by
          rw [← MonoidHom.mem_ker, ker_pairing]
          exact h1
        have e2 : pairing x.left.2 = 1 := by
          rw [← MonoidHom.mem_ker, ker_pairing]
          exact h2
        rw [e1, e2]
      · rw [hr]
        exact iff_of_true (kleinSet_sub_a4Set _ h1) rfl
    · rw [hx]
      exact ⟨rfl, by decide⟩
    · rw [Set.mem_singleton_iff.mp hx]
      refine ⟨?_, ?_⟩
      · show pairing (gT * gS).left.1 = pairing (gT * gS).left.2
        rw [gT_gS_left]
      · rw [gT_gS_left, mul_right]
        exact iff_of_false (by decide) (by decide)

theorem Xs_eq_closure : Xs = Subgroup.closure XsGens := by
  apply le_antisymm
  · intro x hxs
    obtain ⟨v1, hv1, v2, hv2, k, j, e1, e2⟩ := decompose_all _ _ ((pairing_eq_iff _ _).mp hxs)
    rw [decompose_eq x v1 v2 k j e1 e2, mul_assoc _ (gT ^ (j : ℕ))]
    apply mem_closure_of_decompose Set.subset_union_left (Or.inr (Or.inl rfl)) x v1 v2 hv1 hv2
    refine Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure
      (show gT ∈ XsGens from Or.inr (Or.inr (Or.inl rfl)))) _) ?_
    rcases C2Wreath.cases x.right with h | h
    · rw [h, map_one]
      exact Subgroup.one_mem _
    · rw [h, ← gS]
      exact Subgroup.subset_closure (show gS ∈ XsGens from Or.inr (Or.inr (Or.inr rfl)))
  · rw [Subgroup.closure_le]
    rintro x (⟨hr, h1, h2⟩ | hx | hx | hx)
    · show pairing x.left.1 = pairing x.left.2
      have e1 : pairing x.left.1 = 1 := by
        rw [← MonoidHom.mem_ker, ker_pairing]
        exact h1
      have e2 : pairing x.left.2 = 1 := by
        rw [← MonoidHom.mem_ker, ker_pairing]
        exact h2
      rw [e1, e2]
    · rw [hx]
      rfl
    · rw [hx]
      rfl
    · rw [Set.mem_singleton_iff.mp hx]
      rfl

end TwoFourDiagonal
end SymmetricSubgroupAsymptotics
