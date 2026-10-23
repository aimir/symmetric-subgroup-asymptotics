import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms

/-! A literal finite-field embedding commutes with every arithmetic
Frobenius power. This extends automorphisms without replacing either
field by a different model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K]
variable (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] [Algebra (ZMod p) K]

theorem embedding_primeFrobenius_pow (i : F →+* K) (k : ℕ) (x : F) :
    (primeFrobenius K p ^ k) (i x) = i ((primeFrobenius F p ^ k) x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ']
    change primeFrobenius K p ((primeFrobenius K p ^ k) (i x)) =
      i (primeFrobenius F p ((primeFrobenius F p ^ k) x))
    rw [ih, primeFrobenius_apply, primeFrobenius_apply, map_pow]

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms
