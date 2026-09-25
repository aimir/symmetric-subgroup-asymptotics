import SymmetricSubgroupAsymptotics.NormalImageQuotient

/-! The relative second isomorphism theorem retains the original ambient
conjugation. It identifies the heads of N/(N∩K) and NK/K, including the
actual character evaluations on every original element of N. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {A G H : Type*} [Group A] [Group G] [Group H]

/-- Equivariant group equivalences transport the full invariant character
space, not just its dimension. -/
def primeActionCharacterCongr (e : G ≃* H)
    (ρ : A →* MulAut G) (σ : A →* MulAut H)
    (he : ∀ a g, e (ρ a g) = σ a (e g)) :
    primeActionCharacters p σ ≃ₗ[ZMod p] primeActionCharacters p ρ :=
  LinearEquiv.ofBijective (primeActionInflation p e.toMonoidHom ρ σ he)
    ⟨primeActionInflation_injective p e.toMonoidHom ρ σ he e.surjective, by
      intro χ
      let ψ : primeActionCharacters p σ :=
        ⟨χ.1.comp e.symm.toMonoidHom.toAdditive, by
          intro a h
          change χ.1 (Additive.ofMul (e.symm (σ a h))) =
            χ.1 (Additive.ofMul (e.symm h))
          have ht : e.symm (σ a h) = ρ a (e.symm h) := by
            apply e.injective
            rw [e.apply_symm_apply,he,e.apply_symm_apply]
          rw [ht]
          exact χ.2 a (e.symm h)⟩
      refine ⟨ψ,?_⟩
      apply Subtype.ext
      ext g
      change χ.1 (Additive.ofMul (e.symm (e g))) = χ.1 (Additive.ofMul g)
      rw [e.symm_apply_apply]⟩

variable (N K : Subgroup A) [N.Normal] [K.Normal]

theorem normalChainMap_kernel_map :
    N ⊓ K = (normalChainMap K N).ker.map N.subtype := by
  ext x
  constructor
  · rintro ⟨hn,hk⟩
    refine ⟨⟨x,hn⟩,?_,rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := K) x).mpr hk
  · rintro ⟨n,hn,rfl⟩
    refine ⟨n.property,?_⟩
    exact (QuotientGroup.eq_one_iff (N := K) (n:A)).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hn))

def relativeSecondIsomorphism :
    normalChainQuotient (N ⊓ K) N ≃* normalChainQuotient K N :=
  normalSectionQuotientEquiv N (N ⊓ K) (normalChainMap K N)
    (normalChainMap_surjective K N) (normalChainMap_kernel_map N K)

@[simp] theorem relativeSecondIsomorphism_apply (n : N) :
    relativeSecondIsomorphism N K (normalChainMap (N ⊓ K) N n) = normalChainMap K N n :=
  normalSectionQuotientEquiv_apply N (N ⊓ K) (normalChainMap K N)
    (normalChainMap_surjective K N) (normalChainMap_kernel_map N K) n

theorem relativeSecondIsomorphism_equivariant (a : A)
    (n : normalChainQuotient (N ⊓ K) N) :
    relativeSecondIsomorphism N K (normalChainTargetAction (N ⊓ K) N a n) =
      normalChainTargetAction K N a (relativeSecondIsomorphism N K n) := by
  obtain ⟨x,rfl⟩ := normalChainMap_surjective (N ⊓ K) N n
  rw [← normalChainMap_equivariant, relativeSecondIsomorphism_apply,
    relativeSecondIsomorphism_apply, normalChainMap_equivariant]

/-- Both relative heads keep their own literal quotient ambient group.
Surjectivity of A onto those ambients transports precisely the same invariance. -/
def relativeSecondCharacters :
    primeRelativeCharacters p (normalChainQuotient K N) ≃ₗ[ZMod p]
      primeRelativeCharacters p (normalChainQuotient (N ⊓ K) N) :=
  (normalChainTargetCharactersEquiv K N p).symm.trans
    ((primeActionCharacterCongr p (relativeSecondIsomorphism N K)
      (normalChainTargetAction (N ⊓ K) N) (normalChainTargetAction K N)
      (relativeSecondIsomorphism_equivariant N K)).trans
        (normalChainTargetCharactersEquiv (N ⊓ K) N p))

@[simp] theorem relativeSecondCharacters_apply
    (χ : primeRelativeCharacters p (normalChainQuotient K N)) (n : N) :
    (relativeSecondCharacters p N K χ).1
      (Additive.ofMul (normalChainMap (N ⊓ K) N n)) =
        χ.1 (Additive.ofMul (normalChainMap K N n)) := by
  change χ.1 (Additive.ofMul (relativeSecondIsomorphism N K
    (normalChainMap (N ⊓ K) N n))) = _
  rw [relativeSecondIsomorphism_apply]

theorem primeRelativeHead_second_isomorphism :
    Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient (N ⊓ K) N)) =
      Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient K N)) :=
  (relativeSecondCharacters p N K).finrank_eq.symm

end SymmetricSubgroupAsymptotics
