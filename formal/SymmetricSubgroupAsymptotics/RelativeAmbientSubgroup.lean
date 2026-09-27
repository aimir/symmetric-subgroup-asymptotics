import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import SymmetricSubgroupAsymptotics.RelativeSecondIsomorphism

/-!
# Restricting the ambient group of a relative head

Whole-ambient invariant characters remain invariant after restricting the
acting group to a subgroup.  For two original normal subgroups `N,K ◁ A`,
this gives an injection from the relative characters of the physical
intersection `N ⊓ K` in `A` to the relative characters of the same group,
written as `N.subgroupOf K`, in the smaller ambient `K`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {A B G : Type*} [Group A] [Group B] [Group G]

/-- Restrict invariant characters along a homomorphism of acting groups,
without changing the group on which the characters are evaluated. -/
def primeActionCharactersRestrictActingGroup
    (ι : B →* A) (ρ : A →* MulAut G) :
    primeActionCharacters p ρ →ₗ[ZMod p]
      primeActionCharacters p (ρ.comp ι) where
  toFun χ := ⟨χ.1, fun b g => χ.2 (ι b) g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem primeActionCharactersRestrictActingGroup_injective
    (ι : B →* A) (ρ : A →* MulAut G) :
    Function.Injective (primeActionCharactersRestrictActingGroup p ι ρ) := by
  intro χ ψ h
  apply Subtype.ext
  exact congrArg
    (fun z : primeActionCharacters p (ρ.comp ι) => (z : PrimeCharacters p G)) h

variable (N K : Subgroup A)

/-- The physical intersection, viewed either in `A` or inside `K`. -/
def infSubgroupOfEquiv : (N ⊓ K : Subgroup A) ≃* N.subgroupOf K where
  toFun n := ⟨⟨(n : A), n.2.2⟩, n.2.1⟩
  invFun n := ⟨((n : K) : A), ⟨n.2, n.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem infSubgroupOfEquiv_coe (n : (N ⊓ K : Subgroup A)) :
    ((infSubgroupOfEquiv N K n : N.subgroupOf K) : K) =
      ⟨(n : A), n.2.2⟩ := rfl

variable [N.Normal] [K.Normal]

instance subgroupOf_normal : (N.subgroupOf K).Normal := by
  constructor
  intro n hn k
  change (k : A) * ((n : K) : A) * (k : A)⁻¹ ∈ N
  exact Subgroup.Normal.conj_mem inferInstance ((n : K) : A) hn (k : A)

theorem infSubgroupOfEquiv_equivariant (k : K)
    (n : (N ⊓ K : Subgroup A)) :
    infSubgroupOfEquiv N K
        (((normalChainSourceAction (N ⊓ K)).comp K.subtype) k n) =
      normalChainSourceAction (N.subgroupOf K) k (infSubgroupOfEquiv N K n) := by
  rfl

/-- Restrict the ambient conjugation group from `A` to `K`, retaining the
same physical normal intersection through its literal subgroup chart. -/
def primeRelativeCharactersToSubgroupOf :
    primeRelativeCharacters p (N ⊓ K) →ₗ[ZMod p]
      primeRelativeCharacters p (N.subgroupOf K) :=
  (normalChainSourceCharactersEquiv (N.subgroupOf K) p).toLinearMap.comp
    ((primeActionCharacterCongr p (infSubgroupOfEquiv N K)
      ((normalChainSourceAction (N ⊓ K)).comp K.subtype)
      (normalChainSourceAction (N.subgroupOf K))
      (infSubgroupOfEquiv_equivariant N K)).symm.toLinearMap.comp
        ((primeActionCharactersRestrictActingGroup p K.subtype
          (normalChainSourceAction (N ⊓ K))).comp
            (normalChainSourceCharactersEquiv (N ⊓ K) p).symm.toLinearMap))

theorem primeRelativeCharactersToSubgroupOf_injective :
    Function.Injective (primeRelativeCharactersToSubgroupOf p N K) := by
  exact (normalChainSourceCharactersEquiv (N.subgroupOf K) p).injective.comp
    ((primeActionCharacterCongr p (infSubgroupOfEquiv N K)
      ((normalChainSourceAction (N ⊓ K)).comp K.subtype)
      (normalChainSourceAction (N.subgroupOf K))
      (infSubgroupOfEquiv_equivariant N K)).symm.injective.comp
        ((primeActionCharactersRestrictActingGroup_injective p K.subtype
          (normalChainSourceAction (N ⊓ K))).comp
            (normalChainSourceCharactersEquiv (N ⊓ K) p).symm.injective))

/-- Shrinking the ambient conjugation group can only enlarge the relative
character head. -/
theorem primeRelativeHead_inf_le_subgroupOf [Finite A] :
    Module.finrank (ZMod p) (primeRelativeCharacters p (N ⊓ K)) ≤
      Module.finrank (ZMod p) (primeRelativeCharacters p (N.subgroupOf K)) :=
  (primeRelativeCharactersToSubgroupOf p N K).finrank_le_finrank_of_injective
    (primeRelativeCharactersToSubgroupOf_injective p N K)

end SymmetricSubgroupAsymptotics

end
