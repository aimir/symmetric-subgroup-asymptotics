import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineTernaryTailPilot

/-! Bounded prime-power arithmetic after the selected three-row pilot.
Only composite degrees34..1023 are tested: at most32 by10 parameter
choices, independent of any group or subgroup census. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineTernaryTailNumerics

private theorem bounded_receipt : ∀ p : Fin 32, ∀ d : Fin 10,
    p.val.Prime → 2 ≤ d.val → 34 ≤ p.val^d.val → p.val^d.val < 1024 →
    20*((fullAffineOrder p.val d.val).factorization 3 -
      (p.val^d.val).factorization 3) < 3*p.val^d.val := by
  unfold fullAffineOrder fullLinearOrder
  decide +kernel

theorem parameter_bounds {p d : ℕ} (hp : p.Prime) (hd : 2 ≤ d)
    (hs : p^d < 1024) : p < 32 ∧ d < 10 := by
  constructor
  · by_contra hn
    have hh : 1024 ≤ p^d := calc
      1024 = 32^2 := by decide
      _ ≤ p^2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ p^d := pow_le_pow_right₀ hp.one_lt.le hd
    omega
  · by_contra hn
    have hh : 1024 ≤ p^d := calc
      1024 = 2^10 := by decide
      _ ≤ p^10 := Nat.pow_le_pow_left hp.two_le 10
      _ ≤ p^d := pow_le_pow_right₀ hp.one_lt.le (by omega)
    omega

theorem fullAffineOrder_strict_tail {p d : ℕ} (hp : p.Prime)
    (hd : 2 ≤ d) (hf : 34 ≤ p^d) (hs : p^d < 1024) :
    20*((fullAffineOrder p d).factorization 3 - (p^d).factorization 3) < 3*p^d := by
  obtain ⟨hp32,hd10⟩ := parameter_bounds hp hd hs
  exact bounded_receipt ⟨p,hp32⟩ ⟨d,hd10⟩ hp hd hf hs

end SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineTernaryTailNumerics
