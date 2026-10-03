import SymmetricSubgroupAsymptotics.FusionCentralLifts
import SymmetricSubgroupAsymptotics.PrimeRankWeightedTail
import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre

/-!
# Central prime rows on one unchanged complete source

This is the prime-uniform form of `FusionCentralPrefix`.  A literal central
elementary `p`-kernel is counted by the prime-character rank of the original
source.  The next, possibly nonsplit, elementary layer is charged only by its
Schur capacity.  The quotient map and all prime-character columns stay on the
same source, so their joint moment is a subgroup count in the exact shifted
degree `b + q * (s + p * c)`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]

/-- The retained quotient maps together with `c` independent prime-character
columns on the same original source. -/
def fusionPrimeCentralPrefixWeight
    (c : ℕ) (J B : Type*) [Group J] [Group B] : ℝ :=
  (Nat.card (GroupEpimorphism J B) : ℝ) *
    (p : ℝ) ^ (c * Module.finrank (ZMod p) (PrimeCharacters p J))

section CentralKernel

variable {J Q B V : Type} [Group J] [Group Q] [Group B]
variable [Finite J] [Finite Q] [Finite B]
variable [AddCommGroup V] [Module (ZMod p) V] [Finite V]

omit [Finite Q] [Finite B] in
/-- An actual elementary prime kernel has exactly the expected same-source
Hom cardinality. -/
theorem fusionPrimeKernelHom_card
    (π : Q →* B) (E : π.ker ≃* Multiplicative V) :
    Nat.card (J →* π.ker) =
      p ^ (Module.finrank (ZMod p) V *
        Module.finrank (ZMod p) (PrimeCharacters p J)) := by
  rw [Nat.card_congr (E.monoidHomCongrRightEquiv (M := J)),
    primeAbelianizationGroupHom_card p J]
  rw [Nat.mul_comm]

/-- The exact prime-character factor remains attached to the same base map
and to every original survival predicate. -/
theorem fusionCentralPrimeEpimorphism_survival_card_le
    (π : Q →* B) (hπ : Function.Surjective π)
    (hC : FusionCentralKernel π)
    (E : π.ker ≃* Multiplicative V)
    (S : GroupEpimorphism J Q → Prop) :
    Nat.card {f : GroupEpimorphism J Q // S f} ≤
      Nat.card (GroupEpimorphism J B) *
        p ^ (Module.finrank (ZMod p) V *
          Module.finrank (ZMod p) (PrimeCharacters p J)) := by
  simpa only [fusionPrimeKernelHom_card p π E] using
    fusionCentralEpimorphism_survival_card_le π hπ hC S

end CentralKernel

section Envelope

variable {J Q R B V : Type} [Group J] [Group Q] [Group R] [Group B]
variable [Finite J] [Finite Q] [Finite R] [Finite B]
variable [AddCommGroup V] [Module (ZMod p) V] [Finite V]

/-- Central prime prefix followed by one ordinary Schur layer.  The rank
bound is stated on the actual Sylow subgroup of each unchanged base map. -/
theorem fusionPrimeCentralPrefix_survival_card_le
    (π : Q →* R) (hπ : Function.Surjective π)
    (hC : FusionCentralKernel π)
    (EC : π.ker ≃* Multiplicative V)
    (α : R →* B) (hα : Function.Surjective α)
    (M : Rep (ZMod p) B) [Finite M]
    (E : OriginalKernelModuleChart α M)
    (P : ∀ β : GroupEpimorphism J B, Sylow p β.1.ker)
    (S : GroupEpimorphism J Q → Prop) (b : ℝ)
    (hrank : ∀ β : GroupEpimorphism J B,
      (Module.finrank (ZMod p)
        (PrimeAbelianization p (P β : Subgroup β.1.ker)) : ℝ) ≤ b / p) :
    (Nat.card {f : GroupEpimorphism J Q // S f} : ℝ) ≤
      (Nat.card M * Nat.card (groupCohomology.H1 M) : ℝ) *
        (p : ℝ) ^ ((representationSchurCapacity M.ρ / p) * b) *
          fusionPrimeCentralPrefixWeight p
            (Module.finrank (ZMod p) V) J B := by
  have hc := fusionCentralPrimeEpimorphism_survival_card_le p π hπ hC EC S
  have hcR : (Nat.card {f : GroupEpimorphism J Q // S f} : ℝ) ≤
      (Nat.card (GroupEpimorphism J R) : ℝ) *
        (p : ℝ) ^ (Module.finrank (ZMod p) V *
          Module.finrank (ZMod p) (PrimeCharacters p J)) := by
    exact_mod_cast hc
  have hs := fusionEpimorphism_survival_card_le_schur_of_rank_bound
    p α hα M E P (fun _ => True) b hrank
  rw [Nat.card_subtype_true] at hs
  calc
    _ ≤ (Nat.card (GroupEpimorphism J R) : ℝ) *
        (p : ℝ) ^ (Module.finrank (ZMod p) V *
          Module.finrank (ZMod p) (PrimeCharacters p J)) := hcR
    _ ≤ (Nat.card (GroupEpimorphism J B) *
        (Nat.card M * Nat.card (groupCohomology.H1 M) *
          (p : ℝ) ^ (representationSchurCapacity M.ρ * (b / p)))) *
            (p : ℝ) ^ (Module.finrank (ZMod p) V *
              Module.finrank (ZMod p) (PrimeCharacters p J)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by
      unfold fusionPrimeCentralPrefixWeight
      rw [show representationSchurCapacity M.ρ * (b / p) =
        (representationSchurCapacity M.ρ / p) * b by ring]
      ring

end Envelope

/-- Every common-source moment of the retained prime prefix is encoded in
the original faithful cover together with the regular prime markers. -/
theorem fusionPrimeCentralPrefixWeight_moment_le
    {A B : Type} [Group A] [Group B] [Finite B] {s : ℕ}
    (ρ : A →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (π : A →* B) (hπ : Function.Surjective π)
    (b c q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionPrimeCentralPrefixWeight p c J B ^ q) ≤
      (subgroupCount (b + q * (s + p * c)) : ℝ) := by
  have h := jointSourceEpimorphism_primeRank_moment_le
    p ρ hρ π hπ b c q
  unfold fusionPrimeCentralPrefixWeight
  exact_mod_cast h

end SymmetricSubgroupAsymptotics

end
