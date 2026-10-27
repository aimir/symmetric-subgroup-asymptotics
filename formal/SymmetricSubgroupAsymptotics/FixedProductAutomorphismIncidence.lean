import SymmetricSubgroupAsymptotics.FiniteHomogeneousIncidence
import SymmetricSubgroupAsymptotics.OuterFixedElementEvaluationBound
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Commute.Basic

/-! Fixed-product automorphisms are transported only by genuine inner
automorphisms. Their point fibres in a supplied original permutation
representation are compared by powers of the fixed product. No extension
of an abstract automorphism to the permutation domain is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FixedProductAutomorphismIncidence
open OuterFixedElementEvaluationBound

variable {G : Type} {X : Type*} [Group G]

def innerFixed (a g : G) (hc : Commute g a) : fixedAutomorphisms a :=
  ⟨MulAut.conj g,by
    change g * a * g⁻¹ = a
    rw [hc.eq,mul_inv_cancel_right]⟩

def twist (a g : G) (hc : Commute g a) :
    fixedAutomorphisms a ≃ fixedAutomorphisms a where
  toFun f := innerFixed a g hc * f
  invFun f := (innerFixed a g hc)⁻¹ * f
  left_inv f := inv_mul_cancel_left _ _
  right_inv f := mul_inv_cancel_left _ _

theorem twist_apply (a g : G) (hc : Commute g a)
    (f : fixedAutomorphisms a) (x : G) :
    (twist a g hc f).val x = g * f.val x * g⁻¹ := rfl

def fixedPointFibreEquiv (rho : G →* Equiv.Perm X) (x a g : G)
    (hc : Commute g a) (p q : X) (hg : rho g p = q) :
    {f : fixedAutomorphisms a // rho (f.val x) p = p} ≃
      {f : fixedAutomorphisms a // rho (f.val x) q = q} :=
  (twist a g hc).subtypeEquiv (by
    intro f
    have he : rho ((twist a g hc f).val x) q = rho g (rho (f.val x) p) := by
      rw [twist_apply,map_mul,map_mul,map_inv]
      change rho g (rho (f.val x) ((rho g).symm q)) = _
      rw [←hg,(rho g).symm_apply_apply]
    constructor
    · intro hf
      rw [he,hf,hg]
    · intro hf
      apply (rho g).injective
      rw [←he,hf,hg])

theorem fixed_point_incidence_lower [Finite G] [Fintype X]
    (rho : G →* Equiv.Perm X) (x a : G) (p₀ : X) (d : ℕ)
    (htrans : ∀ p q : X, ∃ k : ℤ, rho (a ^ k) p = q)
    (hlower : ∀ f : fixedAutomorphisms a,
      d ≤ Nat.card {p : X // rho (f.val x) p = p}) :
    d * Nat.card (fixedAutomorphisms a) ≤ Nat.card X *
      Nat.card {f : fixedAutomorphisms a // rho (f.val x) p₀ = p₀} := by
  letI : Finite (MulAut G) := Finite.of_injective
    (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective
  apply FiniteHomogeneousIncidence.lower_card_mul_le
    (fun (f : fixedAutomorphisms a) (p : X) => rho (f.val x) p = p) p₀ d hlower
  intro p
  obtain ⟨k,hk⟩ := htrans p₀ p
  exact Nat.card_congr
    (fixedPointFibreEquiv rho x a (a ^ k) ((Commute.refl a).zpow_left k) p₀ p hk).symm

theorem outer_fixed_point_fibre_bound [Finite G] [Fintype X]
    (rho : G →* Equiv.Perm X) (x a : G) (p₀ : X) (d : ℕ)
    (htrans : ∀ p q : X, ∃ k : ℤ, rho (a ^ k) p = q)
    (hlower : ∀ f : fixedAutomorphisms a,
      d ≤ Nat.card {p : X // rho (f.val x) p = p})
    (houter : Nat.card X * Nat.card (PrimitiveSocleRawStructure.Outer G) ≤
      2 * Nat.card (fixedAutomorphisms a)) :
    d * Nat.card (PrimitiveSocleRawStructure.Outer G) ≤
      2 * Nat.card {f : fixedAutomorphisms a // rho (f.val x) p₀ = p₀} := by
  letI : Nonempty X := ⟨p₀⟩
  have hinc := fixed_point_incidence_lower rho x a p₀ d htrans hlower
  have hh : Nat.card X * (d * Nat.card (PrimitiveSocleRawStructure.Outer G)) ≤
      Nat.card X * (2 * Nat.card
        {f : fixedAutomorphisms a // rho (f.val x) p₀ = p₀}) := by
    calc
      _ = d * (Nat.card X * Nat.card (PrimitiveSocleRawStructure.Outer G)) := by ac_rfl
      _ ≤ d * (2 * Nat.card (fixedAutomorphisms a)) := Nat.mul_le_mul_left d houter
      _ = 2 * (d * Nat.card (fixedAutomorphisms a)) := by ac_rfl
      _ ≤ 2 * (Nat.card X * Nat.card
          {f : fixedAutomorphisms a // rho (f.val x) p₀ = p₀}) := Nat.mul_le_mul_left 2 hinc
      _ = _ := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hh Nat.card_pos

theorem zpow_fixes (rho : G →* Equiv.Perm X) (a : G) (p : X)
    (ha : rho a p = p) (k : ℤ) : rho (a ^ k) p = p := by
  let S := (MulAction.stabilizer (Equiv.Perm X) p).comap rho
  have haS : a ∈ S := ha
  have hle : Subgroup.zpowers a ≤ S := Subgroup.zpowers_le.mpr haS
  have hz : a ^ k ∈ Subgroup.zpowers a :=
    Subgroup.mem_zpowers_iff.mpr ⟨k,rfl⟩
  exact hle hz

def imagePointFibreEquiv (rho : G →* Equiv.Perm X) (x a g : G)
    (hc : Commute g a) (base p q : X)
    (hfix : rho g base = base) (hg : rho g p = q) :
    {f : fixedAutomorphisms a // rho (f.val x) base = p} ≃
      {f : fixedAutomorphisms a // rho (f.val x) base = q} :=
  (twist a g hc).subtypeEquiv (by
    intro f
    have hinv : (rho g)⁻¹ base = base := by
      change (rho g).symm base = base
      apply (rho g).injective
      rw [(rho g).apply_symm_apply,hfix]
    have he : rho ((twist a g hc f).val x) base = rho g (rho (f.val x) base) := by
      rw [twist_apply,map_mul,map_mul,map_inv]
      simp only [Equiv.Perm.mul_apply,hinv]
    constructor
    · intro hf
      rw [he,hf,hg]
    · intro hf
      apply (rho g).injective
      rw [←he,hf,hg])

def movedImage (rho : G →* Equiv.Perm X) (x a : G) (base : X)
    (hmoves : ∀ f : fixedAutomorphisms a, rho (f.val x) base ≠ base)
    (f : fixedAutomorphisms a) : {p : X // p ≠ base} :=
  ⟨rho (f.val x) base,hmoves f⟩

def movedImageFibreEquiv (rho : G →* Equiv.Perm X) (x a : G) (base : X)
    (hmoves : ∀ f : fixedAutomorphisms a, rho (f.val x) base ≠ base)
    (p : {p : X // p ≠ base}) :
    {f : fixedAutomorphisms a // movedImage rho x a base hmoves f = p} ≃
      {f : fixedAutomorphisms a // rho (f.val x) base = p.val} :=
  Equiv.subtypeEquivRight (by
    intro f
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h)

theorem fixed_card_eq_moved_fibre [Finite G] [Fintype X]
    (rho : G →* Equiv.Perm X) (x a : G) (base : X)
    (ha : rho a base = base)
    (hmoves : ∀ f : fixedAutomorphisms a, rho (f.val x) base ≠ base)
    (htrans : ∀ p q : {p : X // p ≠ base}, ∃ k : ℤ, rho (a ^ k) p.val = q.val)
    (p₀ : {p : X // p ≠ base}) :
    Nat.card (fixedAutomorphisms a) = Nat.card {p : X // p ≠ base} *
      Nat.card {f : fixedAutomorphisms a // rho (f.val x) base = p₀.val} := by
  letI : Finite (MulAut G) := Finite.of_injective
    (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective
  let e := movedImage rho x a base hmoves
  have hc (p : {p : X // p ≠ base}) :
      Nat.card {f : fixedAutomorphisms a // e f = p} =
        Nat.card {f : fixedAutomorphisms a // rho (f.val x) base = p.val} :=
    Nat.card_congr (movedImageFibreEquiv rho x a base hmoves p)
  have hequal (p : {p : X // p ≠ base}) :
      Nat.card {f : fixedAutomorphisms a // e f = p} =
        Nat.card {f : fixedAutomorphisms a // e f = p₀} := by
    rw [hc p,hc p₀]
    obtain ⟨k,hk⟩ := htrans p₀ p
    exact Nat.card_congr (imagePointFibreEquiv rho x a (a ^ k)
      ((Commute.refl a).zpow_left k) base p₀.val p.val (zpow_fixes rho a base ha k) hk).symm
  exact (FiniteHomogeneousIncidence.card_eq_mul_fibre e p₀ hequal).trans
    (congrArg (fun n : ℕ => Nat.card {p : X // p ≠ base} * n) (hc p₀))

theorem outer_moved_fibre_bound [Finite G] [Fintype X]
    (rho : G →* Equiv.Perm X) (x a : G) (base : X)
    (ha : rho a base = base)
    (hmoves : ∀ f : fixedAutomorphisms a, rho (f.val x) base ≠ base)
    (htrans : ∀ p q : {p : X // p ≠ base}, ∃ k : ℤ, rho (a ^ k) p.val = q.val)
    (p₀ : {p : X // p ≠ base})
    (houter : Nat.card {p : X // p ≠ base} *
      Nat.card (PrimitiveSocleRawStructure.Outer G) ≤
        2 * Nat.card (fixedAutomorphisms a)) :
    Nat.card (PrimitiveSocleRawStructure.Outer G) ≤
      2 * Nat.card {f : fixedAutomorphisms a // rho (f.val x) base = p₀.val} := by
  letI : Nonempty {p : X // p ≠ base} := ⟨p₀⟩
  have hh := houter
  rw [fixed_card_eq_moved_fibre rho x a base ha hmoves htrans p₀] at hh
  have he : 2 * (Nat.card {p : X // p ≠ base} *
      Nat.card {f : fixedAutomorphisms a // rho (f.val x) base = p₀.val}) =
      Nat.card {p : X // p ≠ base} *
        (2 * Nat.card {f : fixedAutomorphisms a // rho (f.val x) base = p₀.val}) := by
    ac_rfl
  rw [he] at hh
  exact Nat.le_of_mul_le_mul_left hh Nat.card_pos

theorem image_moves_of_generates (rho : G →* Equiv.Perm X) (x a : G) (base : X)
    (hgen : Subgroup.closure ({x,a} : Set G) = ⊤)
    (ha : rho a base = base) (hx : rho x base ≠ base)
    (f : fixedAutomorphisms a) : rho (f.val x) base ≠ base := by
  intro hf
  let S := (MulAction.stabilizer (Equiv.Perm X) base).comap
    (rho.comp f.val.toMonoidHom)
  have hle : Subgroup.closure ({x,a} : Set G) ≤ S := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · subst z
      exact hf
    · subst z
      change rho (f.val a) base = base
      rw [f.property]
      exact ha
  rw [hgen] at hle
  have hm : f.val.symm x ∈ S := hle (by trivial)
  change rho (f.val (f.val.symm x)) base = base at hm
  rw [f.val.apply_symm_apply] at hm
  exact hx hm

theorem image_swap_of_involution (rho : G →* Equiv.Perm X) (x a : G)
    (hx : x ^ 2 = 1) (f : fixedAutomorphisms a) (p : X) :
    rho (f.val x) (rho (f.val x) p) = p := by
  have hh : rho (f.val x) ^ 2 = 1 := by
    rw [←map_pow,←map_pow,hx,map_one,map_one]
  rw [pow_two] at hh
  have he := congrArg (fun sigma : Equiv.Perm X => sigma p) hh
  change rho (f.val x) (rho (f.val x) p) = p at he
  exact he

end SymmetricSubgroupAsymptotics.FixedProductAutomorphismIncidence
