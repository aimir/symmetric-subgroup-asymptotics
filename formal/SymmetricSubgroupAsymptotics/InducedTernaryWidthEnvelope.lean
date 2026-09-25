import SymmetricSubgroupAsymptotics.PGroupInducedHead
import SymmetricSubgroupAsymptotics.InducedTernaryEnvelope
import SymmetricSubgroupAsymptotics.TernaryWidthEnvelope

/-! The ternary grid-width bound on the actual Sylow/Mackey pieces of an
original induced subrepresentation. The fibre in each piece is the original
twisted fibre. Restriction and the coordinate filtration retain the original
subrepresentation; no decomposition of that subrepresentation is assumed.

The new width envelope is separate from the Gaussian envelope. No published
prime-power module input is used in the theorems in this file. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

attribute [local instance] inducedMackeyComponentAddCommGroup inducedMackeyComponentModule

/-- The local bound applies to every actual Mackey orbit, including exponent
zero, and to every subrepresentation of its original twisted induced fibre. -/
theorem induced_ternaryLocalWidth_orbit_head_bound
    (p : ℕ) [Fact p.Prime]
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H P : Subgroup G) (hP : IsPGroup 3 P) (ρ : Representation (ZMod p) H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))]
    (M : Subrepresentation (Representation.ind H.subtype ρ))
    (j : DoubleCoset.Quotient (H : Set G) (P : Set G) → ℕ)
    (hindex : ∀ q, (inducedOrbitStabilizer H P q.out).index = 3 ^ j q) :
    Module.finrank (ZMod p)
      (primeActionCharacters p (representationGroupAction M.toRepresentation)) ≤
        ∑ q, Module.finrank (ZMod p) V * ternaryLocalWidth (j q) := by
  letI := induced_finiteDimensional H ρ
  have h := representationCharacterHead_le_coordinates (p := p) (V₀ := M.toSubmodule)
    (fun q => inducedMackeyComponent H P ρ q)
    (M.toRepresentation.comp P.subtype)
    (fun q => Representation.ind (inducedOrbitStabilizer H P q.out).subtype
      (inducedOrbitFibre H P ρ q.out))
    (fun q => Module.finrank (ZMod p) V * ternaryLocalWidth (j q))
    (fun q S => threeGroup_induced_subrepresentationCharacterHead_le
      (q := p) (G₀ := P) (V₀ := V) hP
      (inducedOrbitStabilizer H P q.out) (inducedOrbitFibre H P ρ q.out)
      (j q) (hindex q) S)
    (inducedMackeySubmoduleCoordinate H P ρ M)
    (inducedMackeySubmoduleCoordinate_injective H P ρ M)
  exact (representationCharacterHead_le_restriction (p := p) (V := M.toSubmodule)
    M.toRepresentation P.subtype).trans h

/-- The canonical integer coefficient B(s), formed from the actual index.
The division occurs in ℕ before multiplication by any fibre dimension. -/
def ternaryIndexWidth (s : ℕ) : ℕ :=
  ternaryWidthEnvelope s (s.factorization 3) (largestPrimePower (ordCompl[3] s))

/-- Install the arithmetic factor data from the literal original index. -/
theorem ternaryIndexWidth_factors (s : ℕ) (hs : s ≠ 0) :
    TernaryWidthFactors s (s.factorization 3) (ordCompl[3] s)
      (largestPrimePower (ordCompl[3] s)) where
  eq_mul := (Nat.ordProj_mul_ordCompl_eq_self s 3).symm
  not_dvd := Nat.not_dvd_ordCompl (by decide) hs
  denominator_one := by
    intro hm
    rw [hm]
    simp [largestPrimePower]
  denominator_two := by
    intro hm
    rw [hm]
    norm_num [largestPrimePower, (by decide : Nat.Prime 2).factorization_self]
  denominator_large := fun h1 h2 => largestPrimePower_ge_four (ordCompl[3] s)
    (Nat.ordCompl_pos 3 hs).ne' (Nat.not_dvd_ordCompl (by decide) hs) h1 h2

theorem ternaryIndexWidth_le_third (s : ℕ) (hs : 3 ≤ s) :
    ternaryIndexWidth s ≤ s / 3 :=
  ternaryWidthEnvelope_le_third (ternaryIndexWidth_factors s (by omega)) hs

/-- The integer scalar residuals, with all factor inputs constructed from s. -/
theorem ternaryIndexWidth_scalar_failure_iff (s : ℕ) (hs : 2 ≤ s) :
    9 * s / 20 < ternaryIndexWidth s + 5 * s / 27 ↔ s = 2 ∨ s = 6 ∨ s = 18 :=
  ternaryWidthEnvelope_scalar_failure_iff (ternaryIndexWidth_factors s (by omega)) hs

/-- Restriction to an actual Sylow subgroup supplies all orbit exponents,
their common valuation lower bound, and their exact total size. -/
theorem inducedTernary_head_le_widthCore
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (H : Subgroup G) (ρ : Representation (ZMod 3) H V)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod 3)
      (primeActionCharacters 3 (representationGroupAction M.toRepresentation)) ≤
        Module.finrank (ZMod 3) V * ternaryWidthCore H.index (H.index.factorization 3) := by
  let P : Sylow 3 G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Fintype.ofFinite _
  obtain ⟨j, hj, hkj, hs⟩ := inducedMackeySylow_indices H 3 P
  exact (induced_ternaryLocalWidth_orbit_head_bound 3 H (P : Subgroup G)
    P.isPGroup' ρ M j hj).trans
      (ternaryLocalWidth_weighted_sum_le_core (Module.finrank (ZMod 3) V)
        j H.index (H.index.factorization 3) hkj hs)

/-- The proved coprime branch in integer form. The original prime-power
divisor divides the original index, so division precedes the fibre factor. -/
theorem inducedTernary_coprime_head_bound_nat
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (H : Subgroup G) (ρ : Representation (ZMod 3) H V)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod 3)
      (primeActionCharacters 3 (representationGroupAction M.toRepresentation)) ≤
        Module.finrank (ZMod 3) V *
          (H.index / largestPrimePower (ordCompl[3] H.index)) := by
  obtain ⟨q, hq, hq3, hpow⟩ := largestPrimePower_ordCompl_three_exists H.index
  letI : Fact q.Prime := ⟨hq⟩
  have h := induced_coprime_primePower_head_bound 3 q hq3.symm H ρ M
  rw [hpow] at h
  have hdiv : largestPrimePower (ordCompl[3] H.index) ∣ H.index := by
    rw [← hpow]
    exact Nat.ordProj_dvd H.index q
  have hd := (Nat.le_div_iff_mul_le
    (largestPrimePower_pos (ordCompl[3] H.index))).mpr h
  rwa [Nat.mul_div_assoc _ hdiv] at hd

/-- The integer B-envelope for every actual induced ternary subrepresentation.
Both branches are proved on the original M and original fibre. -/
theorem inducedTernary_head_le_indexWidth
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (H : Subgroup G) (ρ : Representation (ZMod 3) H V)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    Module.finrank (ZMod 3)
      (primeActionCharacters 3 (representationGroupAction M.toRepresentation)) ≤
        Module.finrank (ZMod 3) V * ternaryIndexWidth H.index := by
  unfold ternaryIndexWidth ternaryWidthEnvelope
  rw [mul_min_of_nonneg _ _ (Nat.zero_le _)]
  exact le_min (inducedTernary_head_le_widthCore H ρ M)
    (inducedTernary_coprime_head_bound_nat H ρ M)

/-- The same integer coefficient at the real-valued chief-bound
interface; no real floor is distributed through the original fibre factor. -/
theorem inducedTernary_head_le_indexWidth_real
    {G V : Type} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (H : Subgroup G) (ρ : Representation (ZMod 3) H V)
    (M : Subrepresentation (Representation.ind H.subtype ρ)) :
    (Module.finrank (ZMod 3)
      (primeActionCharacters 3 (representationGroupAction M.toRepresentation)) : ℝ) ≤
        (Module.finrank (ZMod 3) V : ℝ) * (ternaryIndexWidth H.index : ℝ) := by
  exact_mod_cast inducedTernary_head_le_indexWidth H ρ M

end SymmetricSubgroupAsymptotics
