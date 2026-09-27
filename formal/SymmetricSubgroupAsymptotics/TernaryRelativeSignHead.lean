import SymmetricSubgroupAsymptotics.PrimeActionQuotient
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import SymmetricSubgroupAsymptotics.TernarySignInvariantHead

/-!
# Binary sign coordinates kill actual ternary relative heads

The elementary ternary quotient of an arbitrary finite group carries the
original automorphism action.  Actual invariant characters inject into the
head of that representation.  Consequently, jointly faithful coordinates
with nontrivial binary signs annihilate the literal relative character space
of an original normal subgroup, with its whole ambient conjugation action.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {p : ℕ} [Fact p.Prime]
variable {B G : Type} [Group B] [Group G]

/-- An actual invariant prime character factors through the elementary prime
quotient as an intertwining map to the trivial line. -/
def primeActionCharacterToAbelianizationHead [Finite G]
    (α : B →* MulAut G) :
    primeActionCharacters p α →ₗ[ZMod p]
      (primeAbelianizationRepresentation p α).IntertwiningMap
        (Representation.trivial (ZMod p) B (ZMod p)) where
  toFun χ := {
    toLinearMap := primeAbelianizationLift p G χ.1
    isIntertwining' := fun b => by
      apply LinearMap.ext
      intro v
      obtain ⟨g, rfl⟩ := primeAbelianizationMap_surjective p G v
      change primeAbelianizationLift p G χ.1
          (primeAbelianizationRepresentation p α b
            (primeAbelianizationMap p G (Additive.ofMul g.toMul))) =
        primeAbelianizationLift p G χ.1
          (primeAbelianizationMap p G (Additive.ofMul g.toMul))
      rw [primeAbelianizationRepresentation_eval,
        primeAbelianizationLift_apply, primeAbelianizationLift_apply]
      exact χ.2 b g.toMul
  }
  map_add' χ ψ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    obtain ⟨g, rfl⟩ := primeAbelianizationMap_surjective p G v
    rw [Representation.IntertwiningMap.add_toLinearMap]
    change primeAbelianizationLift p G (χ + ψ).1 (primeAbelianizationMap p G g) =
      (primeAbelianizationLift p G χ.1 + primeAbelianizationLift p G ψ.1)
        (primeAbelianizationMap p G g)
    rw [LinearMap.add_apply, primeAbelianizationLift_apply,
      primeAbelianizationLift_apply, primeAbelianizationLift_apply]
    rfl
  map_smul' c χ := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    obtain ⟨g, rfl⟩ := primeAbelianizationMap_surjective p G v
    rw [Representation.IntertwiningMap.toLinearMap_smul]
    change primeAbelianizationLift p G (c • χ).1 (primeAbelianizationMap p G g) =
      (c • primeAbelianizationLift p G χ.1) (primeAbelianizationMap p G g)
    rw [LinearMap.smul_apply, primeAbelianizationLift_apply,
      primeAbelianizationLift_apply]
    rfl

/-- No invariant character is lost when passing to the actual elementary
prime quotient. -/
theorem primeActionCharacterToAbelianizationHead_injective [Finite G]
    (α : B →* MulAut G) :
    Function.Injective (primeActionCharacterToAbelianizationHead (p := p) α) := by
  intro χ ψ h
  apply Subtype.ext
  ext g
  have he := congrArg
    (fun f : (primeAbelianizationRepresentation p α).IntertwiningMap
        (Representation.trivial (ZMod p) B (ZMod p)) =>
      f (primeAbelianizationMap p G g)) h
  change primeAbelianizationLift p G χ.1 (primeAbelianizationMap p G g) =
    primeAbelianizationLift p G ψ.1 (primeAbelianizationMap p G g) at he
  rw [primeAbelianizationLift_apply, primeAbelianizationLift_apply] at he
  exact he

/-- The invariant-character rank is bounded by the representation head of
the original elementary quotient, retaining the same acting group. -/
theorem primeActionCharacterRank_le_abelianizationHead [Finite G]
    (α : B →* MulAut G) :
    Module.finrank (ZMod p) (primeActionCharacters p α) ≤
      Module.finrank (ZMod p)
        ((primeAbelianizationRepresentation p α).IntertwiningMap
          (Representation.trivial (ZMod p) B (ZMod p))) :=
  (primeActionCharacterToAbelianizationHead (p := p) α).finrank_le_finrank_of_injective
    (primeActionCharacterToAbelianizationHead_injective (p := p) α)

/-- Joint nontrivial binary signs on the actual elementary ternary quotient
annihilate the literal relative head of an original normal subgroup.  The
coordinates may have proper images and need not split the quotient. -/
theorem primeRelativeCharacterHead_eq_zero_of_nontrivial_sign_coordinates
    {A ι : Type} [Group A] [Finite A] [Fintype ι]
    (N : Subgroup A) [N.Normal]
    (W : ι → Type)
    [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 3) (W i)]
    [∀ i, FiniteDimensional (ZMod 3) (W i)]
    (χ : ∀ _ : ι, A →* Multiplicative (ZMod 2))
    (hχ : ∀ i, χ i ≠ 1)
    (f : ∀ i,
      (primeAbelianizationRepresentation 3 (normalChainSourceAction N)).IntertwiningMap
        (@ternarySignRepresentation A (W i) _ _ _ (χ i)))
    (hf : Function.Injective (fun v i => f i v)) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 0 := by
  let ρ := primeAbelianizationRepresentation 3 (normalChainSourceAction N)
  have hsign : Module.finrank (ZMod 3)
      (primeActionCharacters (A := A)
        (G := Multiplicative (PrimeAbelianization 3 N)) 3
        (representationGroupAction ρ)) = 0 :=
    representationCharacterHead_eq_zero_of_nontrivial_sign_coordinates
      W ρ χ hχ f hf
  have hinter : Module.finrank (ZMod 3)
      (ρ.IntertwiningMap (Representation.trivial (ZMod 3) A (ZMod 3))) = 0 := by
    rw [← (representationCharacterHeadEquiv ρ).finrank_eq]
    exact hsign
  have hsource := primeActionCharacterRank_le_abelianizationHead
    (p := 3) (normalChainSourceAction N)
  rw [hinter] at hsource
  have hsourceZero : Module.finrank (ZMod 3)
      (primeActionCharacters 3 (normalChainSourceAction N)) = 0 :=
    Nat.eq_zero_of_le_zero hsource
  rw [← (normalChainSourceCharactersEquiv N 3).finrank_eq]
  exact hsourceZero

end SymmetricSubgroupAsymptotics

end
