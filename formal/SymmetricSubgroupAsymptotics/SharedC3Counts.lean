import SymmetricSubgroupAsymptotics.SharedC3
import SymmetricSubgroupAsymptotics.SharedC3LinearCounts

/-!
# Exact shared-C3 fixed-top homomorphism counts

This is the mandatory c=1 audit on actual semidirect-product groups. Both
marks have one shared source; the translations remain distinct actual maps.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

abbrev SharedF4 := GaloisField 2 2
local instance : Fintype SharedF4 := Fintype.ofFinite SharedF4

theorem sharedF4_card : Nat.card SharedF4 = 4 := by
  simpa using GaloisField.card 2 (n := 2) (by norm_num)

theorem sharedC3_top_card : Nat.card SharedF4ˣ = 3 := by
  rw [Nat.card_units,sharedF4_card]

theorem sharedC3_top_cyclic : IsCyclic SharedF4ˣ := inferInstance

private theorem sharedC3_nonidentity_exists : ∃ u : SharedF4ˣ, (u : SharedF4) ≠ 1 := by
  haveI : Nontrivial SharedF4ˣ := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [sharedC3_top_card]; norm_num)
  obtain ⟨u,hu⟩ := exists_ne (1 : SharedF4ˣ)
  exact ⟨u,fun h ↦ hu (Units.ext h)⟩

private def sharedC3Unit : SharedF4ˣ := Classical.choose sharedC3_nonidentity_exists
private theorem sharedC3Unit_ne : (sharedC3Unit : SharedF4) ≠ 1 :=
  Classical.choose_spec sharedC3_nonidentity_exists

/-- The actual F4^r semidirect C3 group, with scalar action. -/
abbrev SharedC3Group (r : ℕ) := ScalarAffineGroup SharedF4 (Fin r → SharedF4)

/-- Actual homomorphisms over the one fixed common C3 top map. -/
abbrev SharedC3FixedTopHom (r m : ℕ) :=
  ScalarTopLift (K := SharedF4) (V := Fin r → SharedF4) (W := Fin m → SharedF4)

theorem sharedC3Group_card (r : ℕ) : Nat.card (SharedC3Group r) = 3*4^r := by
  have h4 : Fintype.card SharedF4 = 4 := by simpa only [Nat.card_eq_fintype_card] using sharedF4_card
  rw [SemidirectProduct.card,sharedC3_top_card]
  simp [h4,mul_comm]

/-- Actual fixed-top maps have independent linear and coboundary parameters
on this same source; neither parameter is a quotient by conjugacy. -/
def sharedC3FixedTopHomEquiv (r m : ℕ) :
    SharedC3FixedTopHom r m ≃
      ((Fin r → SharedF4) →ₗ[SharedF4] (Fin m → SharedF4)) × (Fin m → SharedF4) :=
  scalarTopLiftEquiv sharedC3Unit sharedC3Unit_ne

/-- The full coboundary factor 4^m is present in actual homomorphisms. -/
theorem sharedC3_fixedTopHom_card (r m : ℕ) :
    Nat.card (SharedC3FixedTopHom r m) = 4^(m*(r+1)) := by
  have h4 : Fintype.card SharedF4 = 4 := by simpa only [Nat.card_eq_fintype_card] using sharedF4_card
  rw [Nat.card_congr (sharedC3FixedTopHomEquiv r m),Nat.card_prod,
    finiteField_linearMap_card, h4]
  simp only [Nat.card_fun,Nat.card_fin,sharedF4_card]
  rw [← pow_add]
  congr 1

/-- Actual onto fixed-top maps retain every coboundary parameter. -/
def sharedC3SurjectiveFixedTopHomEquiv (r m : ℕ) :
    {f : SharedC3FixedTopHom r m // Function.Surjective f.1} ≃
      {L : (Fin r → SharedF4) →ₗ[SharedF4] (Fin m → SharedF4) // Function.Surjective L} ×
        (Fin m → SharedF4) :=
  scalarSurjectiveTopLiftEquiv sharedC3Unit sharedC3Unit_ne

/-- Exact onto-lift fixture, also valid when m>r (both sides are zero). -/
theorem sharedC3_surjectiveFixedTopHom_card (r m : ℕ) :
    Nat.card {f : SharedC3FixedTopHom r m // Function.Surjective f.1} =
      4^m * ∏ i : Fin m, (4^r-4^(i : ℕ)) := by
  have h4 : Fintype.card SharedF4 = 4 := by simpa only [Nat.card_eq_fintype_card] using sharedF4_card
  rw [Nat.card_congr (sharedC3SurjectiveFixedTopHomEquiv r m),Nat.card_prod,
    finiteField_surjective_linearMap_card,h4]
  simp [h4,mul_comm]

/-- Two marks are pairs of actual maps on the same F4^r semidirect C3;
this does not replace that source by two independently chosen groups. -/
theorem sharedC3_two_fixedTop_marks_card (r m₁ m₂ : ℕ) :
    Nat.card (SharedC3FixedTopHom r m₁ × SharedC3FixedTopHom r m₂) =
      4^((m₁+m₂)*(r+1)) := by
  rw [Nat.card_prod,sharedC3_fixedTopHom_card,sharedC3_fixedTopHom_card,← pow_add]
  congr 1
  ring

end SymmetricSubgroupAsymptotics
