import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-! Unique product coordinates retain literal fixedness under a central
semilinear difference. The central difference stays entirely in the
normalizing/diagonal factor; no fixed lift is assumed. These group-only
lemmas apply to every actual root-system realization. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGCentralTwistedProductCoordinates

theorem shifted_product_factors_injective {G C : Type*} [Group G] [Group C]
    (B V : Subgroup G) (W : G) (e : C →* G) (hei : Function.Injective e)
    (hdis : Disjoint B V) (hC : ∀ c, MulAut.conj W (e c) ∈ V) :
    Function.Injective (fun p : B × C => (p.1.val : G) * W * e p.2) := by
  rintro ⟨b, v⟩ ⟨b', v'⟩ he
  change b.val * W * e v = b'.val * W * e v' at he
  have hc : b'.val⁻¹ * b.val = MulAut.conj W (e (v' * v⁻¹)) := by
    change b'.val⁻¹ * b.val = W * e (v' * v⁻¹) * W⁻¹
    rw [map_mul, map_inv]
    calc
      _ = b'.val⁻¹ * (b.val * W * e v) * (e v)⁻¹ * W⁻¹ := by group
      _ = _ := by rw [he]; group
  have hb : b'.val⁻¹ * b.val = 1 := Subgroup.disjoint_def.mp hdis
    (B.mul_mem (B.inv_mem b'.property) b.property) (hc ▸ hC (v' * v⁻¹))
  have hbb : b = b' := Subtype.ext (inv_mul_eq_one.mp hb).symm
  have hvv : v = v' := by
    apply hei
    rw [hbb] at he
    exact mul_left_cancel he
  exact Prod.ext hbb hvv

theorem twisted_product_values {G C : Type*} [Group G] [Group C]
    (tau : G →* G) (B : Subgroup G) (W z : G) (e : C →* G)
    (hinj : Function.Injective (fun p : B × C => (p.1.val : G) * W * e p.2))
    (b bt bz : B) (v vt : C) (hbt : bt.val = tau b.val) (hbz : bz.val = z * b.val)
    (hvt : e vt = tau (e v)) (hW : tau W = W)
    (htwist : tau (b.val * W * e v) = z * (b.val * W * e v)) :
    tau b.val = z * b.val ∧ tau (e v) = e v := by
  have hp : bt.val * W * e vt = bz.val * W * e v := by
    calc
      _ = tau (b.val * W * e v) := by rw [map_mul, map_mul, hW, hbt, hvt]
      _ = z * (b.val * W * e v) := htwist
      _ = _ := by rw [hbz]; simp only [mul_assoc]
  have he := hinj (a₁ := (bt, vt)) (a₂ := (bz, v)) hp
  exact ⟨hbt.symm.trans ((congrArg (fun p => p.1.val) he).trans hbz),
    hvt.symm.trans (congrArg (fun p => e p.2) he)⟩

theorem twisted_diagonal_values {G : Type*} [Group G]
    (tau : G →* G) (U D : Subgroup G)
    (hinj : Function.Injective (fun p : U × D => (p.1.val : G) * p.2.val))
    (z : G) (u ut : U) (d dt dz : D)
    (hut : ut.val = tau u.val) (hdt : dt.val = tau d.val) (hdz : dz.val = z * d.val)
    (hcomm : Commute z u.val) (htwist : tau (u.val * d.val) = z * (u.val * d.val)) :
    tau u.val = u.val ∧ tau d.val = z * d.val := by
  have hp : ut.val * dt.val = u.val * dz.val := by
    calc
      _ = tau (u.val * d.val) := by rw [map_mul, hut, hdt]
      _ = z * (u.val * d.val) := htwist
      _ = _ := by rw [← mul_assoc, hcomm.eq, mul_assoc, hdz]
  have he := hinj (a₁ := (ut, dt)) (a₂ := (u, dz)) hp
  exact ⟨hut.symm.trans (congrArg (fun p => p.1.val) he),
    hdt.symm.trans ((congrArg (fun p => p.2.val) he).trans hdz)⟩

theorem center_normalizes_subgroup {G : Type*} [Group G]
    (H P : Subgroup G) (hPH : P ≤ H) (z : H) (hz : z ∈ Subgroup.center H) :
    z.val ∈ Subgroup.normalizer (P : Set G) := by
  have he (x : G) (hx : x ∈ P) : z.val*x*z.val⁻¹ = x := by
    have hh := congrArg (fun y : H => y.val)
      (Subgroup.mem_center_iff.mp hz ⟨x,hPH hx⟩)
    change x*z.val = z.val*x at hh
    rw [←hh,mul_assoc,mul_inv_cancel,mul_one]
  have hm : P.map (MulAut.conj z.val).toMonoidHom = P := by
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change z.val*y*z.val⁻¹ ∈ P
      rw [he y hy]
      exact hy
    · intro hx
      exact ⟨x,hx,he x hx⟩
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  exact congrArg (fun Q : Subgroup G => (Q : Set G)) hm

end SymmetricSubgroupAsymptotics.CFSGCentralTwistedProductCoordinates
