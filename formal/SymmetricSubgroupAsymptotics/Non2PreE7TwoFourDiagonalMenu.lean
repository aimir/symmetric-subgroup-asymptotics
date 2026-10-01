import SymmetricSubgroupAsymptotics.Non2PreE7TwoFourDiagonalGroup

/-!
# The literal normal menus of `Xc`, `Xg`, `Xs`

The diagonal projection `π₀(x₁, x₂) = x₁ v(x₁⁻¹ 3) x₁⁻¹ x₂`, where `v(j)` is
the Klein involution sending `3` to `j`, is a homomorphism `Xs → S₄` with
kernel the diagonal `Δ = {(v, v) : v ∈ V₄}` on each block-exchange layer.

* `Xs → S₄ × C₂` and `Xc → A₄ × C₂` (with the block exchange) are onto with
  kernel `Δ`, and every nontrivial normal subgroup contains `Δ`.
* For `Xg` the element `n = (1, (1 2 3))` normalizes `Xg` and its powers
  carry `Δ` to the three minimal normal subgroups `Δ_k`; the projections
  `π₀ ∘ conj(n⁻ᵏ)` are onto `S₄` with kernel `Δ_k`.

Every nontrivial normal subgroup meets the self-centralizing base `V₄ × V₄`,
and the nonzero vectors of the base generate one of these minimal subgroups.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace TwoFourDiagonal

open Equiv NaturalS4 C2Wreath SemidirectProduct

/-! ## The diagonal projection on the literal pairs -/

/-- The Klein involution sending `3` to `j`. -/
def vOf (j : Fin 4) : Perm (Fin 4) :=
  if j = 3 then 1 else if j = 2 then c1 else if j = 1 then c2 else c3

/-- The diagonal projection formula. -/
def pi0Fun (x1 x2 : Perm (Fin 4)) : Perm (Fin 4) := vOf (x1 3) * x2

/-- The literal pairs agreeing modulo `V₄`. -/
def xsPairs : Finset (Perm (Fin 4) × Perm (Fin 4)) :=
  Finset.univ.filter (fun p => pairFun p.1 = pairFun p.2)

theorem vOf_mul : ∀ x y : Perm (Fin 4), vOf ((x * y) 3) = vOf (x 3) * x * vOf (y 3) * x⁻¹ := by
  decide +kernel

theorem vOf_klein : ∀ u ∈ kleinSet, vOf (u 3) = u := by decide

theorem vOf_mem : ∀ x : Perm (Fin 4), vOf (x 3) ∈ kleinSet := by decide

theorem pairFun_klein : ∀ x y : Perm (Fin 4), pairFun x = pairFun y → x⁻¹ * y ∈ kleinSet := by
  decide +kernel

theorem pi0_ker_pair : ∀ x1 x2 : Perm (Fin 4), pairFun x1 = pairFun x2 →
    (pi0Fun x1 x2 = 1 ↔ (x1 ∈ kleinSet ∧ x2 = x1)) := by decide +kernel

theorem pi0_section : ∀ y : Perm (Fin 4),
    pairFun (vOf (y 3) * y) = pairFun y ∧ pi0Fun y (vOf (y 3) * y) = y := by decide +kernel

theorem pi0_even_pair : ∀ x1 x2 : Perm (Fin 4), x1 ∈ a4Set → pairFun x1 = pairFun x2 →
    pi0Fun x1 x2 ∈ a4Set := by decide +kernel

theorem pi0_one : pi0Fun 1 1 = 1 := by decide

/-- The first multiplication layer. -/
theorem pi0_mul_one (x1 x2 y1 y2 : Perm (Fin 4)) (hx : pairFun x1 = pairFun x2) :
    pi0Fun (x1 * y1) (x2 * y2) = pi0Fun x1 x2 * pi0Fun y1 y2 := by
  have hw := pairFun_klein _ _ hx
  set w := x1⁻¹ * x2 with hwdef
  have hx2 : x2 = x1 * w := by rw [hwdef]; group
  have hc := kleinSet_comm _ (vOf_mem y1) _ hw
  unfold pi0Fun
  rw [vOf_mul, hx2]
  calc vOf (x1 3) * x1 * vOf (y1 3) * x1⁻¹ * (x1 * w * y2)
      = vOf (x1 3) * x1 * (vOf (y1 3) * w) * y2 := by group
    _ = vOf (x1 3) * x1 * (w * vOf (y1 3)) * y2 := by rw [hc]
    _ = vOf (x1 3) * (x1 * w) * (vOf (y1 3) * y2) := by group

/-- The block-exchange multiplication layer. -/
theorem pi0_mul_gen (x1 x2 y1 y2 : Perm (Fin 4)) (hx : pairFun x1 = pairFun x2)
    (hy : pairFun y1 = pairFun y2) :
    pi0Fun (x1 * y2) (x2 * y1) = pi0Fun x1 x2 * pi0Fun y1 y2 := by
  have hw := pairFun_klein _ _ hx
  have hu := pairFun_klein _ _ hy
  set w := x1⁻¹ * x2 with hwdef
  set u := y1⁻¹ * y2 with hudef
  have hx2 : x2 = x1 * w := by rw [hwdef]; group
  have hy2 : y2 = y1 * u := by rw [hudef]; group
  have hu' : y1 * u * y1⁻¹ ∈ kleinSet := kleinSet_conj y1 u hu
  have hb' : vOf (y2 3) = vOf (y1 3) * (y1 * u * y1⁻¹) := by
    rw [hy2, vOf_mul, vOf_klein u hu]
    group
  have hc1 := kleinSet_comm _ (vOf_mem y1) _ hw
  have hc2 := kleinSet_comm _ hu' _ hw
  unfold pi0Fun
  rw [vOf_mul, hb', hx2, hy2]
  calc vOf (x1 3) * x1 * (vOf (y1 3) * (y1 * u * y1⁻¹)) * x1⁻¹ * (x1 * w * y1)
      = vOf (x1 3) * x1 * (vOf (y1 3) * ((y1 * u * y1⁻¹) * w)) * y1 := by group
    _ = vOf (x1 3) * x1 * (vOf (y1 3) * (w * (y1 * u * y1⁻¹))) * y1 := by rw [hc2]
    _ = vOf (x1 3) * x1 * ((vOf (y1 3) * w) * (y1 * u * y1⁻¹)) * y1 := by group
    _ = vOf (x1 3) * x1 * ((w * vOf (y1 3)) * (y1 * u * y1⁻¹)) * y1 := by rw [hc1]
    _ = vOf (x1 3) * (x1 * w) * (vOf (y1 3) * (y1 * u)) := by group

theorem mem_xsPairs {x : W4} (hx : x ∈ Xs) : x.left ∈ xsPairs := by
  rw [xsPairs, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (pairing_eq_iff _ _).mp hx⟩

theorem mem_Xs_of_pair {p : Perm (Fin 4) × Perm (Fin 4)} (hp : p ∈ xsPairs)
    (g : Multiplicative (ZMod 2)) : (inl p * inr g : W4) ∈ Xs := by
  show pairing (inl p * inr g : W4).left.1 = pairing (inl p * inr g : W4).left.2
  rw [left_mul_of_one _ _ rfl]
  simp only [left_inl, left_inr, mul_one]
  exact (pairing_eq_iff _ _).mpr (Finset.mem_filter.mp hp).2

/-- `π₀ : Xs → S₄`. -/
def pi0 : Xs →* Perm (Fin 4) where
  toFun x := pi0Fun (x : W4).left.1 (x : W4).left.2
  map_one' := pi0_one
  map_mul' x y := by
    show pi0Fun ((x : W4) * y).left.1 ((x : W4) * y).left.2 = _
    have hx : pairFun (x : W4).left.1 = pairFun (x : W4).left.2 :=
      (pairing_eq_iff _ _).mp x.2
    have hy : pairFun (y : W4).left.1 = pairFun (y : W4).left.2 :=
      (pairing_eq_iff _ _).mp y.2
    rcases C2Wreath.cases (x : W4).right with h | h
    · rw [left_mul_of_one _ _ h]
      exact pi0_mul_one _ _ _ _ hx
    · rw [left_mul_of_gen _ _ h]
      exact pi0_mul_gen _ _ _ _ hx hy

theorem pi0_apply (x : Xs) : pi0 x = pi0Fun (x : W4).left.1 (x : W4).left.2 := rfl

/-- The block exchange on any subgroup. -/
def blockHom (X : Subgroup W4) : X →* Multiplicative (ZMod 2) :=
  (rightHom : W4 →* Multiplicative (ZMod 2)).comp X.subtype

/-! ## The base and its centralizer -/

/-- The base `V₄ × V₄` as a subgroup. -/
def VW : Subgroup W4 where
  carrier := baseSet
  one_mem' := ⟨rfl, by decide, by decide⟩
  mul_mem' := by
    rintro x y ⟨hx, hx1, hx2⟩ ⟨hy, hy1, hy2⟩
    refine ⟨by rw [mul_right, hx, hy, one_mul], ?_, ?_⟩
    · rw [left_mul_of_one _ _ hx]
      exact kleinSet_mul _ _ hx1 hy1
    · rw [left_mul_of_one _ _ hx]
      exact kleinSet_mul _ _ hx2 hy2
  inv_mem' := by
    rintro x ⟨hx, hx1, hx2⟩
    refine ⟨by rw [inv_right, hx, inv_one], ?_, ?_⟩
    · rw [left_inv_of_one _ hx]
      exact kleinSet_inv _ hx1
    · rw [left_inv_of_one _ hx]
      exact kleinSet_inv _ hx2

theorem eq_inl_of_right (x : W4) (h : x.right = 1) : x = inl x.left := by
  conv_lhs => rw [← inl_left_mul_inr_right x, h, map_one, mul_one]

theorem inl_mul_inl (p q : Perm (Fin 4) × Perm (Fin 4)) :
    (inl p : W4) * inl q = inl (p * q) := (map_mul _ p q).symm

theorem VW_selfCentralizing (x : W4) (hx : ∀ v ∈ VW, x * v = v * x) : x ∈ VW := by
  rcases C2Wreath.cases x.right with h | h
  · refine ⟨h, ?_, ?_⟩
    · have hc : ∀ v (hv : v ∈ kleinSet), x.left.1 * v = v * x.left.1 := by
        intro v hv
        have := hx (inl (v, 1)) ⟨rfl, hv, by exact (by decide : (1 : Perm (Fin 4)) ∈ kleinSet)⟩
        rw [eq_inl_of_right x h, inl_mul_inl, inl_mul_inl] at this
        have := congrArg (fun p : Perm (Fin 4) × Perm (Fin 4) => p.1) (inl_injective this)
        simpa using this
      exact centralizer_kleinSet _ (hc c1 (by decide)) (hc c2 (by decide)) (hc c3 (by decide))
    · have hc : ∀ v (hv : v ∈ kleinSet), x.left.2 * v = v * x.left.2 := by
        intro v hv
        have := hx (inl (1, v)) ⟨rfl, by exact (by decide : (1 : Perm (Fin 4)) ∈ kleinSet), hv⟩
        rw [eq_inl_of_right x h, inl_mul_inl, inl_mul_inl] at this
        have := congrArg (fun p : Perm (Fin 4) × Perm (Fin 4) => p.2) (inl_injective this)
        simpa using this
      exact centralizer_kleinSet _ (hc c1 (by decide)) (hc c2 (by decide)) (hc c3 (by decide))
  · exfalso
    have hv0 := hx (inl (c1, 1)) ⟨rfl, by decide, by decide⟩
    have := congrArg (fun y : W4 => y.left.1) hv0
    simp only [left_mul_of_gen _ _ h, left_mul_of_one _ _ (right_inl _), left_inl] at this
    simp at this
    exact c1_ne_one (by
      have h2 := congrArg (fun σ => σ * (x.left.1)⁻¹) this
      simpa using h2.symm)

/-- In a group, a normal subgroup meeting a self-centralizing normal
subgroup trivially is trivial. -/
theorem inf_ne_bot_of_selfCentralizing {G : Type*} [Group G] (V : Subgroup G) [hV : V.Normal]
    (hcent : ∀ x : G, (∀ v ∈ V, x * v = v * x) → x ∈ V)
    (N : Subgroup G) [hN : N.Normal] (hNb : N ≠ ⊥) : N ⊓ V ≠ ⊥ := by
  intro h
  apply hNb
  have hNV : N ≤ V := by
    intro x hx
    apply hcent
    intro v hv
    have hc : x * v * x⁻¹ * v⁻¹ ∈ N ⊓ V := by
      refine ⟨?_, V.mul_mem (hV.conj_mem v hv x) (V.inv_mem hv)⟩
      have h2 : v * x⁻¹ * v⁻¹ ∈ N := hN.conj_mem x⁻¹ (N.inv_mem hx) v
      have h3 : x * (v * x⁻¹ * v⁻¹) ∈ N := N.mul_mem hx h2
      simpa [mul_assoc] using h3
    rw [h] at hc
    have h1 : x * v * x⁻¹ * v⁻¹ = 1 := (Subgroup.mem_bot).mp hc
    calc x * v = (x * v * x⁻¹ * v⁻¹) * (v * x) := by group
      _ = v * x := by rw [h1, one_mul]
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ N ⊓ V := ⟨hx, hNV hx⟩
  rw [h] at this
  exact this

end TwoFourDiagonal
end SymmetricSubgroupAsymptotics
