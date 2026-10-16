import SymmetricSubgroupAsymptotics.TernarySignedPermutationSubgroupSocles
import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-! Actual signed ternary affine subgroups with coprime cyclic block image
have quotient-socle bound two. The binary sign image has normal bound two;
the ternary kernel has cyclic invariant submodules. Coprime primary types
combine by a maximum, removing the conservative third generator without
asserting normal-generator inheritance from an ambient wreath. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TernarySignedCyclicCoprimeQuotientSocles
open TernarySignedPermutationSubgroupSocles
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

variable {R X Q : Type} [Group R] [Finite R] [IsCyclic R] [MulAction R X]
  [Fintype X] [DecidableEq X] [Group Q]
  (E : Subrepresentation
    (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := X)))
  (K : Subgroup (TernarySignedPermutationSubgroupSocles.Model E))

theorem sign_coprime (hR : Nat.Coprime 3 (Nat.card R)) :
    Nat.Coprime 3 (Nat.card (SignModel E)) := by
  rw [SemidirectProduct.card,Nat.card_congr Multiplicative.toAdd,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.coprime_mul_iff_right.mpr
    ⟨(by decide : Nat.Coprime 3 2).pow_right _,hR⟩

theorem socle_of_surjective (c : R) (x : X)
    (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y)
    (hsurj : Function.Surjective (blocks E K))
    (hR : Nat.Coprime 3 (Nat.card R))
    (π : K →* Q) (hπ : Function.Surjective π) : SocleNormalGeneratorBound Q 2 := by
  let rho := imageRepresentation (TernarySignedPermutationSubgroupSocles.linearAction E) K
  have hu : UniformSubrepresentationGeneratorBound rho 1 := uniform_image E K c x hcycle hsurj
  let idMap : rho.IntertwiningMap rho :=
    { toLinearMap := LinearMap.id
      isIntertwining' _ := rfl }
  have hg : RepresentationGeneratedBy rho 1 :=
    representationGeneratedBy_of_injective_of_uniform hu idMap (fun _ _ h => h)
  have hcop : Nat.Coprime 3 (Nat.card (TernarySignedPermutationSubgroupSocles.Image E K)) :=
    (sign_coprime E hR).of_dvd_right
      (TernarySignedPermutationSubgroupSocles.Image E K).card_subgroup_dvd_card
  apply LinearSemidirectSubgroupSocles.coprime_socle_of_surjective
    (TernarySignedPermutationSubgroupSocles.linearAction E) K hcop 1 2 hg ?_ π hπ
  intro L hL
  letI := hL
  apply image_normalGen_le E K c x hcycle hsurj 1 ?_ L
  intro A hA
  letI := hA
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic A

theorem quotientSocle (c : R) (x : X)
    (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y)
    (hsurj : Function.Surjective (blocks E K))
    (hR : Nat.Coprime 3 (Nat.card R))
    (N : Subgroup K) [N.Normal] : SocleNormalGeneratorBound (K ⧸ N) 2 :=
  socle_of_surjective E K c x hcycle hsurj hR
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end SymmetricSubgroupAsymptotics.TernarySignedCyclicCoprimeQuotientSocles

end
