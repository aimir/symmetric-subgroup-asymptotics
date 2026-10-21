import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor
import Mathlib.Tactic.NormNum

/-! Small elementary GL-order arithmetic, separated from every action and
catalogue. The kernel reduces at most45 by6 numerical parameter choices. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem affine_small_receipt : ∀ p : Fin 45,∀ d : Fin 6,
    p.val.Prime → 0<d.val → p.val^d.val<45 →
    (4≤p.val^d.val → p.val^d.val≠9 →
      10*(fullAffineOrder p.val d.val).factorization 3≤3*p.val^d.val) ∧
    (p.val^d.val≠3 → p.val^d.val≠4 →
      20*((fullAffineOrder p.val d.val).factorization 3-
        (p.val^d.val).factorization 3)<3*p.val^d.val) ∧
    (p.val^d.val=9 → 3*(fullAffineOrder p.val d.val).factorization 3≤p.val^d.val) := by
  unfold fullAffineOrder fullLinearOrder
  decide +kernel

theorem prime_power_small_parameter_bounds {p d : ℕ}
    (hp : p.Prime) (hd : 0<d) (hs : p^d<45) : p<45 ∧ d<6 := by
  have hpd : p≤p^d := by
    simpa only [pow_one] using pow_le_pow_right₀ (hp.one_lt.le : 1≤p) hd
  have hdim : d<6 := by
    by_contra hn
    have h6 : 6≤d := by omega
    have h64 : 64≤p^d := calc
      64=2^6 := by decide
      _ ≤ p^6 := Nat.pow_le_pow_left hp.two_le 6
      _ ≤ p^d := pow_le_pow_right₀ (hp.one_lt.le : 1≤p) h6
    omega
  exact ⟨by omega,hdim⟩

theorem fullAffineOrder_small_ternary_bounds {p d : ℕ}
    (hp : p.Prime) (hd : 0<d) (hs : p^d<45) :
    (4≤p^d → p^d≠9 → 10*(fullAffineOrder p d).factorization 3≤3*p^d) ∧
    (p^d≠3 → p^d≠4 →
      20*((fullAffineOrder p d).factorization 3-(p^d).factorization 3)<3*p^d) ∧
    (p^d=9 → 3*(fullAffineOrder p d).factorization 3≤p^d) := by
  obtain ⟨hp45,hd6⟩ := prime_power_small_parameter_bounds hp hd hs
  exact affine_small_receipt ⟨p,hp45⟩ ⟨d,hd6⟩ hp hd hs

end SymmetricSubgroupAsymptotics
