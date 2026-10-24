import SymmetricSubgroupAsymptotics.GroupActionInertia
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel

/-! SAME-linear-part affine actions dominate inertia orbits as well as
point orbits. Joint affine fixed sets are empty or actual translates of
the SAME joint linear fixed subgroup. The fixed points of the inertia
action retain the actual commuting pair, and Burnside counts them. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.AffineInertiaOrbitDomination
open GroupActionInertia

variable {G X V : Type*} [Group G] [AddCommGroup V]
    [MulAction G X] [DistribMulAction G V]

def jointFixed (Y : Type*) [MulAction G Y] (g h : G) : Set Y :=
  {y | g • y = y ∧ h • y = y}

private theorem difference_fixed (e : X ≃ V) (t : G → V)
    (hlinear : ∀ (g : G) (x : X), e (g • x) = t g + g • e x)
    (g : G) (x y : X) (hx : g • x = x) (hy : g • y = y) :
    g • (e x - e y) = e x - e y := by
  calc
    _ = g • e x - g • e y := smul_sub _ _ _
    _ = (t g + g • e x) - (t g + g • e y) := by abel
    _ = e x - e y := by rw [← hlinear g x, ← hlinear g y, hx, hy]

private theorem translated_fixed (e : X ≃ V) (t : G → V)
    (hlinear : ∀ (g : G) (x : X), e (g • x) = t g + g • e x)
    (g : G) (x : X) (hx : g • x = x) (v : V) (hv : g • v = v) :
    g • e.symm (e x + v) = e.symm (e x + v) := by
  apply e.injective
  rw [hlinear]
  simp only [e.apply_symm_apply, smul_add, hv]
  rw [← add_assoc, ← hlinear g x, hx]

def jointFixedTranslate (e : X ≃ V) (t : G → V)
    (hlinear : ∀ (g : G) (x : X), e (g • x) = t g + g • e x)
    (g h : G) (x₀ : jointFixed X g h) : jointFixed X g h ≃ jointFixed V g h where
  toFun x := ⟨e x.val - e x₀.val,
    difference_fixed e t hlinear g x.val x₀.val x.property.1 x₀.property.1,
    difference_fixed e t hlinear h x.val x₀.val x.property.2 x₀.property.2⟩
  invFun v := ⟨e.symm (e x₀.val + v.val),
    translated_fixed e t hlinear g x₀.val x₀.property.1 v.val v.property.1,
    translated_fixed e t hlinear h x₀.val x₀.property.2 v.val v.property.2⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    change e (e.symm (e x₀.val + (e x.val - e x₀.val))) = e x.val
    rw [e.apply_symm_apply]
    abel
  right_inv v := by
    apply Subtype.ext
    change e (e.symm (e x₀.val + v.val)) - e x₀.val = v.val
    rw [e.apply_symm_apply]
    abel

theorem jointFixed_card_le (e : X ≃ V) (t : G → V)
    (hlinear : ∀ (g : G) (x : X), e (g • x) = t g + g • e x) (g h : G) :
    Nat.card (jointFixed X g h) ≤ Nat.card (jointFixed V g h) := by
  by_cases hx : ∃ x : X, g • x = x ∧ h • x = x
  · obtain ⟨x, hx⟩ := hx
    exact (Nat.card_congr (jointFixedTranslate e t hlinear g h ⟨x, hx⟩)).le
  · letI : IsEmpty (jointFixed X g h) := ⟨fun x => hx ⟨x.val, x.property⟩⟩
    have hz : Nat.card (jointFixed X g h) = 0 :=
      Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hz]
    exact Nat.zero_le _

def fixedInertiaEquiv (h : G) :
    MulAction.fixedBy (inertia G X) h ≃
      Σ a : {a : G // a * h = h * a}, jointFixed X a.val h where
  toFun p := by
    have he : h * p.val.val.1 * h⁻¹ = p.val.val.1 :=
      congrArg (fun z : inertia G X => z.val.1) p.property
    have hm := congrArg (fun a : G => a * h) he
    have hc : p.val.val.1 * h = h * p.val.val.1 := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm.symm
    have hx : h • p.val.val.2 = p.val.val.2 :=
      congrArg (fun z : inertia G X => z.val.2) p.property
    exact ⟨⟨p.val.val.1, hc⟩, ⟨p.val.val.2, p.val.property, hx⟩⟩
  invFun p := ⟨⟨(p.1.val, p.2.val), p.2.property.1⟩, by
    apply Subtype.ext
    apply Prod.ext
    · change h * p.1.val * h⁻¹ = p.1.val
      rw [← p.1.property, mul_assoc, mul_inv_cancel, mul_one]
    · exact p.2.property.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> rfl
  right_inv p := by
    rcases p with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    rfl

theorem fixed_inertia_card_le [Finite G] [Finite X] [Finite V]
    (e : X ≃ V) (t : G → V)
    (hlinear : ∀ (g : G) (x : X), e (g • x) = t g + g • e x) (h : G) :
    Nat.card (MulAction.fixedBy (inertia G X) h) ≤
      Nat.card (MulAction.fixedBy (inertia G V) h) := by
  letI : Fintype {a : G // a * h = h * a} := Fintype.ofFinite _
  calc
    _ = ∑ a : {a : G // a * h = h * a}, Nat.card (jointFixed X a.val h) := by
      rw [← Nat.card_sigma]
      exact Nat.card_congr (fixedInertiaEquiv (X := X) h)
    _ ≤ ∑ a : {a : G // a * h = h * a}, Nat.card (jointFixed V a.val h) :=
      Finset.sum_le_sum (fun a _ => jointFixed_card_le e t hlinear a.val h)
    _ = _ := by
      rw [← Nat.card_sigma]
      exact (Nat.card_congr (fixedInertiaEquiv (X := V) h)).symm

theorem inertia_orbit_card_le [Finite G] [Finite X] [Finite V]
    (e : X ≃ V) (t : G → V)
    (hlinear : ∀ (g : G) (x : X), e (g • x) = t g + g • e x) :
    Nat.card (MulAction.orbitRel.Quotient G (inertia G X)) ≤
      Nat.card (MulAction.orbitRel.Quotient G (inertia G V)) := by
  letI : Fintype G := Fintype.ofFinite _
  have hX : (∑ g : G, Nat.card (MulAction.fixedBy (inertia G X) g)) =
      Nat.card (MulAction.orbitRel.Quotient G (inertia G X)) * Nat.card G := by
    rw [← Nat.card_sigma,
      Nat.card_congr (MulAction.sigmaFixedByEquivOrbitsProdGroup G (inertia G X)),
      Nat.card_prod]
  have hV : (∑ g : G, Nat.card (MulAction.fixedBy (inertia G V) g)) =
      Nat.card (MulAction.orbitRel.Quotient G (inertia G V)) * Nat.card G := by
    rw [← Nat.card_sigma,
      Nat.card_congr (MulAction.sigmaFixedByEquivOrbitsProdGroup G (inertia G V)),
      Nat.card_prod]
  have hsum : (∑ g : G, Nat.card (MulAction.fixedBy (inertia G X) g)) ≤
      ∑ g : G, Nat.card (MulAction.fixedBy (inertia G V) g) :=
    Finset.sum_le_sum (fun g _ => fixed_inertia_card_le e t hlinear g)
  rw [hX, hV] at hsum
  exact Nat.le_of_mul_le_mul_right hsum (Nat.card_pos (α := G))

end SymmetricSubgroupAsymptotics.AffineInertiaOrbitDomination
