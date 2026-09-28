import SymmetricSubgroupAsymptotics.Non2LiftBound
import SymmetricSubgroupAsymptotics.PrimeAbelianization
import Mathlib.RepresentationTheory.Intertwining

/-!
# A regular-module bound on the same original kernel

If a target module embeds in one copy of the actual left regular module,
evaluation at the identity injects its equivariant kernel homomorphisms
into the scalar characters of the literal kernel of the original top map.
Surjectivity of that same top map supplies every regular coordinate.

No semisimplicity, splitting, or source-kernel quotient action is assumed.
The lift corollary retains the full module and H1 factors.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {J B Q : Type} [Group J] [Group B] [Group Q]

/-- The identity coefficient of the actual embedded kernel homomorphism. -/
def regularKernelCharacter (β : J →* B) (M : Rep (ZMod p) B)
    (F : M.ρ.IntertwiningMap (Representation.leftRegular (ZMod p) B))
    (f : EquivariantKernelHom β M) : PrimeCharacters p β.ker where
  toFun x := F (f.1 x) 1
  map_zero' := by simp only [map_zero, Finsupp.zero_apply]
  map_add' x y := by simp only [map_add, Finsupp.add_apply]

/-- Equivariance recovers each coefficient from the identity coefficient
on an actual conjugate in the same original kernel. -/
theorem regularKernelCharacter_injective (β : J →* B)
    (hβ : Function.Surjective β) (M : Rep (ZMod p) B)
    (F : M.ρ.IntertwiningMap (Representation.leftRegular (ZMod p) B))
    (hF : Function.Injective F) :
    Function.Injective (regularKernelCharacter p β M F) := by
  intro f g h
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  apply hF
  apply Finsupp.ext
  intro b
  obtain ⟨j, hj⟩ := hβ b⁻¹
  have he := DFunLike.congr_fun h
    (Additive.ofMul (quotientKernelConjugate β j x.toMul))
  change F (f.1 (Additive.ofMul (quotientKernelConjugate β j x.toMul))) 1 =
    F (g.1 (Additive.ofMul (quotientKernelConjugate β j x.toMul))) 1 at he
  rw [f.2 j x.toMul, g.2 j x.toMul, F.isIntertwining, F.isIntertwining] at he
  rw [Representation.ofMulAction_apply, Representation.ofMulAction_apply] at he
  change F (f.1 x) ((β j)⁻¹ * 1) = F (g.1 x) ((β j)⁻¹ * 1) at he
  rwa [hj, inv_inv, mul_one] at he

/-- A regular embedding costs the scalar-character count of the actual
source kernel, rather than the cardinality of a replacement source. -/
theorem equivariantKernelHom_card_le_regular [Finite J]
    (β : J →* B) (hβ : Function.Surjective β) (M : Rep (ZMod p) B)
    (F : M.ρ.IntertwiningMap (Representation.leftRegular (ZMod p) B))
    (hF : Function.Injective F) :
    Nat.card (EquivariantKernelHom β M) ≤ Nat.card (PrimeCharacters p β.ker) :=
  Nat.card_le_card_of_injective (regularKernelCharacter p β M F)
    (regularKernelCharacter_injective p β hβ M F hF)

/-- The same bound in the exact prime-character rank convention. -/
theorem equivariantKernelHom_card_le_regular_rank [Finite J]
    (β : J →* B) (hβ : Function.Surjective β) (M : Rep (ZMod p) B)
    (F : M.ρ.IntertwiningMap (Representation.leftRegular (ZMod p) B))
    (hF : Function.Injective F) :
    Nat.card (EquivariantKernelHom β M) ≤
      p ^ Module.finrank (ZMod p) (PrimeCharacters p β.ker) := by
  have h := equivariantKernelHom_card_le_regular p β hβ M F hF
  rwa [Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := PrimeCharacters p β.ker), Nat.card_zmod] at h

/-- Every original surviving lift is bounded, including an empty or
nonsplit fibre. The module and H1 constants have not been discarded. -/
theorem homomorphicLift_survival_card_le_regular [Finite J] [Finite Q]
    (π : Q →* B) (β : J →* B) (hβ : Function.Surjective β)
    (M : Rep (ZMod p) B) [Finite M] (E : OriginalKernelModuleChart π M)
    (F : M.ρ.IntertwiningMap (Representation.leftRegular (ZMod p) B))
    (hF : Function.Injective F) (S : HomomorphicLift π β → Prop) :
    Nat.card {f : HomomorphicLift π β // S f} ≤
      Nat.card M * Nat.card (groupCohomology.H1 M) *
        Nat.card (PrimeCharacters p β.ker) := by
  exact (homomorphicLift_survival_card_le π β hβ M E S).trans
    (Nat.mul_le_mul_left _ (equivariantKernelHom_card_le_regular p β hβ M F hF))

end SymmetricSubgroupAsymptotics

end
