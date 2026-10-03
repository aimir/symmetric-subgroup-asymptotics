import SymmetricSubgroupAsymptotics.OriginalCentralCutExtension
import SymmetricSubgroupAsymptotics.PrimeCentralPrefix

/-!
# Prime-uniform original central-cut fusion

Quotient a literal extension by a selected invariant prime subspace.  The
first kernel is central and is retained as same-source prime characters; the
second kernel is the unchanged quotient representation.  No splitting of
either extension is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.OriginalPrimeCentralCutFusion
open OriginalCentralCutExtension

variable (p : ℕ) [Fact p.Prime]
variable {B : Type} [Group B]
variable (A : Rep (ZMod p) B)
    (C : {C : Submodule (ZMod p) A // C ≤ A.ρ.invariants})

def capacity : ℝ := representationSchurCapacity (quotientModule A C).ρ

def liftConstant : ℝ :=
  (Nat.card (quotientModule A C) *
    Nat.card (groupCohomology.H1 (quotientModule A C)) : ℝ)

def prefixDegree (s : ℕ) : ℕ :=
  s + p * Module.finrank (ZMod p) C.1

def momentWeight (J : Type*) [Group J] : ℝ :=
  fusionPrimeCentralPrefixWeight p (Module.finrank (ZMod p) C.1) J B

theorem liftConstant_nonneg : 0 ≤ liftConstant p A C := by
  unfold liftConstant
  positivity

/-- One original faithful cover supplies every retained common-source
moment. -/
theorem momentWeight_moment_le
    [Finite B] {T : Type} [Group T] {s : ℕ}
    (ρ : T →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (σ : T →* B) (hσ : Function.Surjective σ)
    (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        momentWeight p A C J ^ q) ≤
      (subgroupCount (b + q * prefixDegree p A C s) : ℝ) := by
  simpa only [momentWeight, prefixDegree] using
    fusionPrimeCentralPrefixWeight_moment_le p ρ hρ σ hσ b
      (Module.finrank (ZMod p) C.1) q

variable {Q : Type} [Group Q] [Finite Q] [Finite B] [Finite A]
    (π : Q →* B) (hπ : Function.Surjective π)
    (E : OriginalKernelModuleChart π A)

include hπ E in
/-- The whole actual surviving family uses the unchanged original quotient.
The fixed central part is not charged to the pointwise Schur exponent. -/
theorem original_survival_card_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b)))
    (S : GroupEpimorphism J Q → Prop) :
    (Nat.card {f : GroupEpimorphism J Q // S f} : ℝ) ≤
      liftConstant p A C *
        (p : ℝ) ^ ((capacity p A C / p) * (b : ℝ)) *
          momentWeight p A C J := by
  letI : Finite (quotientModule A C) :=
    Finite.of_surjective C.1.mkQ C.1.mkQ_surjective
  let P : ∀ β : GroupEpimorphism J B, Sylow p β.1.ker :=
    fun _ => Classical.arbitrary _
  exact fusionPrimeCentralPrefix_survival_card_le p
    (first π A E C) (first_surjective π A E C)
    (first_central π A E C) (centralEquiv π A E C)
    (base π A E C) (base_surjective π A E C hπ)
    (quotientModule A C) (quotientChart π A E C) P S (b : ℝ)
    (fun β => by
      calc
        (Module.finrank (ZMod p)
            (PrimeAbelianization p (P β : Subgroup β.1.ker)) : ℝ) ≤
            ((b / p : ℕ) : ℝ) := by
          exact_mod_cast
            originalQuotientKernelSylow_primeAbelianization_rank_le
              p J β (P β)
        _ ≤ (b : ℝ) / p := Nat.cast_div_le)

end SymmetricSubgroupAsymptotics.OriginalPrimeCentralCutFusion

end
