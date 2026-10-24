import SymmetricSubgroupAsymptotics.FiniteBilinearPrefixOrbits
import Mathlib.Tactic.Linarith

/-! A finite faithful action preserving an actual right-nondegenerate
bilinear form has at most q^(n(n+1)/2) elements. This counts basis
stabilizer orbits and uses no classical group order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteBilinearIsometryOrderBound
open Module
open FiniteBilinearPrefixOrbits

def triangular : ℕ → ℕ
  | 0 => 0
  | n+1 => n+1+triangular n

theorem triangular_eq (n : ℕ) : triangular n = n*(n+1)/2 := by
  have h : triangular n * 2 = n*(n+1) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [triangular]
      nlinarith
  exact Nat.eq_div_of_mul_eq_right (by decide : (2:ℕ)≠0) (by simpa only [Nat.mul_comm] using h)

theorem card_le_of_separating_pairing {F V G : Type*} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [Group G] [Finite G]
    {n : ℕ} (b : Basis (Fin n) F V)
    (rho : G →* (V ≃ₗ[F] V)) (hinj : Function.Injective rho)
    (B : V → V → F)
    (hsep : ∀ x y : V, (∀ i : Fin n, B (b i) x = B (b i) y) → x = y)
    (hpres : ∀ g : G, ∀ x y : V, B (rho g x) (rho g y) = B x y) :
    Nat.card G ≤ Nat.card F ^ (n*(n+1)/2) := by
  have hcount (d : ℕ) : ∀ k : ℕ, k+d=n →
      Nat.card (prefixSubgroup rho b k) ≤ Nat.card F ^ triangular d := by
    induction d with
    | zero =>
      intro k hk
      have hk' : k=n := by omega
      subst k
      rw [prefix_end_card rho b hinj]
      rfl
    | succ d ih =>
      intro k hk
      have hk' : k<n := by omega
      have hn : n-k=d+1 := by omega
      calc
        Nat.card (prefixSubgroup rho b k) ≤
            Nat.card F ^ (n-k) * Nat.card (prefixSubgroup rho b (k+1)) :=
          next_step_card rho b B hsep hpres k hk'
        _ ≤ Nat.card F ^ (n-k) * Nat.card F ^ triangular d :=
          Nat.mul_le_mul_left _ (ih (k+1) (by omega))
        _ = Nat.card F ^ triangular (d+1) := by
          rw [hn, ← pow_add]
          rfl
  have h := hcount n 0 (by omega)
  rw [prefix_zero_card rho b, triangular_eq] at h
  exact h

theorem card_le_of_basis {F V G : Type*} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [Group G] [Finite G]
    {n : ℕ} (b : Basis (Fin n) F V)
    (rho : G →* (V ≃ₗ[F] V)) (hinj : Function.Injective rho)
    (B : LinearMap.BilinForm F V)
    (hB : ∀ v : V, (∀ w : V, B w v = 0) → v = 0)
    (hpres : ∀ g : G, ∀ x y : V, B (rho g x) (rho g y) = B x y) :
    Nat.card G ≤ Nat.card F ^ (n*(n+1)/2) := by
  apply card_le_of_separating_pairing b rho hinj (fun x y => B x y) _ hpres
  intro x y hxy
  apply sub_eq_zero.mp
  apply hB
  intro w
  have hl : (B.flip (x-y) : V →ₗ[F] F) = 0 := by
    apply b.ext
    intro i
    change B (b i) (x-y)=0
    rw [map_sub]
    exact sub_eq_zero.mpr (hxy i)
  exact LinearMap.congr_fun hl w

theorem card_le_pow_finrank {F V G : Type*} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [Finite V] [Group G] [Finite G]
    (rho : G →* (V ≃ₗ[F] V)) (hinj : Function.Injective rho)
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (hpres : ∀ g : G, ∀ x y : V, B (rho g x) (rho g y) = B x y) :
    Nat.card G ≤ Nat.card F ^
      (Module.finrank F V * (Module.finrank F V + 1) / 2) :=
  card_le_of_basis (Module.finBasis F V) rho hinj B hB.2 hpres

end SymmetricSubgroupAsymptotics.FiniteBilinearIsometryOrderBound
