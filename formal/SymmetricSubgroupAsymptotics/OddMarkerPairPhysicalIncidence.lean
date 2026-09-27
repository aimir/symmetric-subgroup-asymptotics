import SymmetricSubgroupAsymptotics.OddMarkerPairModelEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The exact one-third natural-marker incidence

For every retained complete binary exterior, one full natural `S_3`
orbit has the same model cardinality as one additional full `C_2` pair
orbit.  Passing to original permutation subgroups contributes the actual
normalizers and occurrence factorials.  Consequently the normalized
natural-marker family is exactly one third of the normalized family of
binary subgroups pointed at an actual pair orbit.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.OddMarkerPairPhysicalIncidence

open RepeatedMarkerMergedProfile
open OddMarkerPairModelEquiv
open PermutationPairOrbitMarks

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a))) (p : ℕ)

abbrev OddModelPoints := OrbitProfilePoints
  (OddPoints Ω) (OddMultiplicity m p)

abbrev OddPhysical :=
  RepeatedOddMarkerPhysicalProfile.PhysicalFamily
    (BasePoints Ω) (BaseMultiplicity m p) (BaseAction Ω U) 1
    (OddModelPoints Ω m p)

abbrev BinaryPhysical := BinaryDuplicatePairProfile.Physical Ω m U (p+1)

private theorem sign_isPGroup : IsPGroup 2 RepeatedMarkerMergedProfile.Sign := by
  intro x
  refine ⟨1, ?_⟩
  simpa only [pow_one] using binary_mul_pow_two x

private theorem baseAction_isPGroup (hU : ∀ a, IsPGroup 2 (U a)) :
    ∀ i, IsPGroup 2 (BaseAction Ω U i) := by
  intro i
  cases i with
  | inl _ => exact (sign_isPGroup.of_equiv binaryMarkerLocalEquiv)
  | inr a => exact hU a

private theorem baseAction_transitive
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y) :
    ∀ i (x y : BasePoints Ω i), ∃ u : BaseAction Ω U i,
      (u : Equiv.Perm (BasePoints Ω i)) x = y :=
  RepeatedMarkerMergedProfile.action_transitive Ω U htrans

private theorem baseAction_separated
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    OrbitActionTypesSeparated (BasePoints Ω) (BaseAction Ω U) :=
  RepeatedMarkerMergedProfile.action_separated Ω U hsep hdegree

theorem oddPhysical_card
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Nat.card (OddPhysical Ω m U p) : ℚ) =
      (((3 + 2*p + exteriorDegree Ω m).factorial : ℕ) : ℚ) *
        Nat.card (OddModel Ω m U p) /
        ((6 : ℚ) * (2 : ℚ)^p * p.factorial * exteriorDenominator Ω m U) := by
  have h := RepeatedOddMarkerPhysicalBinary.card_physical_rat
    (BasePoints Ω) (BaseMultiplicity m p) (BaseAction Ω U) 1
    (Equiv.refl (OddModelPoints Ω m p))
    (baseAction_isPGroup Ω U hU)
    (baseAction_transitive Ω U htrans)
    (baseAction_separated Ω U hsep hdegree)
  have hmodel := RepeatedOddMarkerPhysicalProfile.model_card
    (BasePoints Ω) (BaseMultiplicity m p) (BaseAction Ω U) 1
    (orbitProfileProduct_isPGroup (BaseMultiplicity m p) (BaseAction Ω U)
      (baseAction_isPGroup Ω U hU))
  rw [RepeatedMarkerMergedProfile.degree Ω m p] at h
  unfold RepeatedOddMarkerPhysicalProfile.exteriorDenominator at h
  rw [RepeatedMarkerMergedProfile.denominator Ω m U p] at h
  rw [← hmodel] at h
  norm_num at h ⊢
  convert h using 1 <;> ring

private theorem factorial_ne_zero (n : ℕ) : ((n.factorial : ℕ) : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

private theorem exteriorDenominator_ne_zero :
    exteriorDenominator Ω m U ≠ 0 := by
  unfold exteriorDenominator
  apply ne_of_gt
  apply Finset.prod_pos
  intro a _
  exact mul_pos (pow_pos (Nat.cast_pos.mpr Nat.card_pos) _)
    (Nat.cast_pos.mpr (Nat.factorial_pos _))

/-- The original physical identity.  The right side points a binary
subgroup at each of its actual two-point orbits; no model coordinate is
used as the mark. -/
theorem normalized_odd_pair_incidence
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Nat.card (OddPhysical Ω m U p) : ℚ) /
        (3 + 2*p + exteriorDegree Ω m).factorial =
      (1 / 3 : ℚ) *
        ((∑ H : BinaryPhysical Ω m U p,
          (Nat.card (PairOrbit H.val) : ℚ)) /
            (2*(p+1) + exteriorDegree Ω m).factorial) := by
  rw [oddPhysical_card Ω m U p hU htrans hsep hdegree,
    BinaryDuplicatePairProfile.physical_pointed_sum Ω m U (p+1) htrans hdegree,
    BinaryDuplicatePairProfile.physical_card Ω m U (p+1) htrans hsep hdegree,
    model_card Ω m U p hU]
  have hfodd := factorial_ne_zero (3 + 2*p + exteriorDegree Ω m)
  have hfbin := factorial_ne_zero (2*(p+1) + exteriorDegree Ω m)
  have hfp := factorial_ne_zero p
  have hfp1 := factorial_ne_zero (p+1)
  have hE := exteriorDenominator_ne_zero Ω m U
  have hp : ((p+1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hpow : (2 : ℚ)^p ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpow1 : (2 : ℚ)^(p+1) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show ((p+1).factorial : ℚ) = (p+1) * (p.factorial : ℚ) by
    rw [Nat.factorial_succ]; push_cast; rfl]
  field_simp [hfodd, hfbin, hfp, hfp1, hE, hp, hpow, hpow1] <;>
    push_cast <;> ring

end SymmetricSubgroupAsymptotics.OddMarkerPairPhysicalIncidence

end
