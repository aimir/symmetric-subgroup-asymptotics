import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import SymmetricSubgroupAsymptotics.PGroupCoinvariantGenerators
import Mathlib.Data.ZMod.QuotientGroup

/-! A literal element whose fourth power fixes every original point and
whose square fixes none gives a quarter-degree bound for every natural
permutation submodule. The witness is checked in the original action; no
claim that all nonelementary transitive binary groups admit one is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G X : Type} [Group G] [MulAction G X]

/-- The two original-action tests force every cyclic orbit to have four
points, even when the original element has a nontrivial action kernel. -/
theorem cyclicOrbit_card_four_of_fourth_fixed_square_free
    (g : G) (hfour : ∀ x : X, g ^ 4 • x = x)
    (hsquare : ∀ x : X, g ^ 2 • x ≠ x) (x : X) :
    Nat.card (MulAction.orbit (Subgroup.zpowers g) x) = 4 := by
  have hd : MulAction.period g x ∣ 2 ^ 2 := by
    exact MulAction.pow_smul_eq_iff_period_dvd.mp (hfour x)
  obtain ⟨j, hj, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hj2 : j = 2 := by
    interval_cases j
    · have hp : MulAction.period g x ∣ 2 := by rw [he]; norm_num
      exact False.elim (hsquare x (MulAction.pow_smul_eq_iff_period_dvd.mpr hp))
    · have hp : MulAction.period g x ∣ 2 := by rw [he]; norm_num
      exact False.elim (hsquare x (MulAction.pow_smul_eq_iff_period_dvd.mpr hp))
    · rfl
  have hperiod : MulAction.period g x = 4 := by simpa [hj2] using he
  calc
    _ = Nat.card (ZMod (Function.minimalPeriod (g • ·) x)) :=
      Nat.card_congr (MulAction.orbitZPowersEquiv g x)
    _ = Function.minimalPeriod (g • ·) x := Nat.card_zmod _
    _ = 4 := hperiod

/-- The cyclic orbit count is degree divided by four in the same action. -/
theorem cyclicOrbitCount_eq_div_four_of_fourth_fixed_square_free [Finite X]
    (g : G) (hfour : ∀ x : X, g ^ 4 • x = x)
    (hsquare : ∀ x : X, g ^ 2 • x ≠ x) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X) = Nat.card X / 4 := by
  have hm := cyclicOrbitCount_mul_of_orbit_card g 4
    (cyclicOrbit_card_four_of_fourth_fixed_square_free g hfour hsquare)
  rw [← hm, Nat.mul_div_cancel _ (by decide : 0 < 4)]

/-- Every original natural submodule has invariant-form head at most a
quarter of the original point degree. The field is arbitrary. -/
theorem permutationSubrepresentationHead_le_quarter_of_semiregular_four
    {k : Type} [Field k] [Finite X]
    (g : G) (hfour : ∀ x : X, g ^ 4 • x = x)
    (hsquare : ∀ x : X, g ^ 2 • x ≠ x)
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Module.finrank k
      (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
        Nat.card X / 4 := by
  exact (permutation_subrepresentationHead_le_cyclicOrbitCount M g).trans_eq
    (cyclicOrbitCount_eq_div_four_of_fourth_fixed_square_free g hfour hsquare)

/-- In defining characteristic the same witness supplies actual module
generators, uniformly over all original permutation subrepresentations. -/
theorem pGroup_permutationSubrepresentationGeneratedBy_quarter_of_semiregular_four
    {p : ℕ} [Fact p.Prime] [Finite X] (hG : IsPGroup p G)
    (g : G) (hfour : ∀ x : X, g ^ 4 • x = x)
    (hsquare : ∀ x : X, g ^ 2 • x ≠ x) :
    ∀ M : Subrepresentation (permutationFunctionRepresentation (ZMod p) G X),
      RepresentationGeneratedBy M.toRepresentation (Nat.card X / 4) := by
  letI := Fintype.ofFinite X
  exact pGroup_uniformSubrepresentationGeneratorBound_of_head_le hG
    (permutationFunctionRepresentation (ZMod p) G X) (Nat.card X / 4)
    (permutationSubrepresentationHead_le_quarter_of_semiregular_four g hfour hsquare)

end SymmetricSubgroupAsymptotics
