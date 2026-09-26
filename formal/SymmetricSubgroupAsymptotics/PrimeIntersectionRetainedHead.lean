import SymmetricSubgroupAsymptotics.FiniteQuotientDerivedIntersection
import SymmetricSubgroupAsymptotics.PrimeRetainedCommutatorHead

/-! An original normal N has central quotient directions over B=N∩G′.
When the actual prime-evaluation kernel lies in G′, these directions have
exponent p. Retained characters on B must annihilate both original p-th
powers and original mixed commutators. In particular, central quotient
directions do not justify discarding the power obstruction. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G]

/-- Normality is in the whole original group, so every original mixed
commutator belongs to the exact derived intersection. -/
theorem normal_mixed_le_derivedIntersection (N : Subgroup G) [N.Normal] :
    ⁅N, (⊤ : Subgroup G)⁆ ≤ N ⊓ commutator G :=
  le_inf (Subgroup.commutator_le_left N ⊤)
    (Subgroup.commutator_mono le_top le_rfl)

/-- The actual image of N in G/(N∩G′) is central. No splitting or
commutativity of N or of G′ is assumed. -/
theorem derivedIntersectionQuotient_le_center (N : Subgroup G) [N.Normal] :
    normalChainQuotient (N ⊓ commutator G) N ≤
      Subgroup.center (G ⧸ (N ⊓ commutator G)) := by
  have hle : N ≤ quotientCenterPreimage (N ⊓ commutator G) := by
    rw [← quotientCenterPreimage_eq_inf_commutator N]
    exact le_quotientCenterPreimage N
  rintro _ ⟨n, hn, rfl⟩
  exact hle hn

/-- These directions meet the image of the actual derived group only
at identity; the complete original N has not been replaced by G′. -/
theorem derivedIntersectionQuotient_inf_derived_eq_bot
    (N : Subgroup G) [N.Normal] :
    normalChainQuotient (N ⊓ commutator G) N ⊓
      normalChainQuotient (N ⊓ commutator G) (commutator G) = ⊥ := by
  apply Subgroup.comap_injective
    (QuotientGroup.mk'_surjective (N ⊓ commutator G))
  change ((N.map (QuotientGroup.mk' (N ⊓ commutator G))) ⊓
      ((commutator G).map (QuotientGroup.mk' (N ⊓ commutator G)))).comap
        (QuotientGroup.mk' (N ⊓ commutator G)) =
      (⊥ : Subgroup (G ⧸ (N ⊓ commutator G))).comap
        (QuotientGroup.mk' (N ⊓ commutator G))
  rw [Subgroup.comap_inf, QuotientGroup.comap_map_mk',
    QuotientGroup.comap_map_mk', MonoidHom.comap_bot, QuotientGroup.ker_mk',
    sup_eq_right.mpr (show N ⊓ commutator G ≤ N from inf_le_left),
    sup_eq_right.mpr (show N ⊓ commutator G ≤ commutator G from inf_le_right)]

variable (p : ℕ) [Fact p.Prime]

/-- The original evaluation-kernel condition supplies power membership,
not the vanishing of arbitrary B characters on those powers. -/
theorem normal_pow_mem_derivedIntersection_of_evaluationKernel_le
    (N : Subgroup G) [N.Normal]
    (hkernel : (primeAbelianizationGroupMap p G).ker ≤ commutator G) (n : N) :
    (n : G) ^ p ∈ N ⊓ commutator G :=
  ⟨N.pow_mem n.2 p, hkernel
    (primeRelativeRadical_le_ambient_evaluation_ker p N
      (pow_mem_primeRelativeRadical p N n))⟩

/-- Together with centrality, this is the actual elementary quotient
direction statement. Its representatives and powers are still original. -/
theorem derivedIntersectionQuotient_pow_eq_one
    (N : Subgroup G) [N.Normal]
    (hkernel : (primeAbelianizationGroupMap p G).ker ≤ commutator G)
    (x : normalChainQuotient (N ⊓ commutator G) N) : x ^ p = 1 := by
  obtain ⟨n, rfl⟩ := normalChainMap_surjective (N ⊓ commutator G) N x
  apply Subtype.ext
  change (QuotientGroup.mk' (N ⊓ commutator G) (n : G)) ^ p = 1
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (N := N ⊓ commutator G) _).mpr
    (normal_pow_mem_derivedIntersection_of_evaluationKernel_le p N hkernel n)

variable (B N : Subgroup G) [B.Normal] [N.Normal]

/-- The power is viewed in the same original B, not as a coordinate
label or a chosen power in an abstract quotient extension. -/
def normalChainPowerElement (hpower : ∀ n : N, (n : G) ^ p ∈ B) (n : N) : B :=
  ⟨(n : G) ^ p, hpower n⟩

/-- Necessary original power equations for extendibility from B to N. -/
def normalChainPowerAnnihilator (hpower : ∀ n : N, (n : G) ^ p ∈ B) :
    Submodule (ZMod p) (primeRelativeCharacters p B) where
  carrier := {χ | ∀ n : N,
    χ.1 (Additive.ofMul (normalChainPowerElement p B N hpower n)) = 0}
  zero_mem' := by intro n; rfl
  add_mem' := by
    intro χ ψ hχ hψ n
    change χ.1 _ + ψ.1 _ = 0
    rw [hχ, hψ, add_zero]
  smul_mem' := by
    intro c χ hχ n
    change c • χ.1 _ = 0
    rw [hχ, smul_zero]

/-- Restriction of an original N character kills n^p even when the
corresponding B character is not itself a restriction from all of G. -/
theorem normalChainRetainedCharacters_le_powerAnnihilator (hBN : B ≤ N)
    (hpower : ∀ n : N, (n : G) ^ p ∈ B) :
    normalChainRetainedCharacters B N p hBN ≤
      normalChainPowerAnnihilator p B N hpower := by
  rintro χ ⟨ψ, rfl⟩ n
  rw [normalChainRestriction_apply_original]
  have hz := (mem_primeRelativeRadical_iff p N ((n : G) ^ p)).mp
    (pow_mem_primeRelativeRadical p N n)
  exact hz.2 (normalChainSourceCharactersEquiv N p ψ)

/-- Both necessary tests are retained. Equality with the extendible
restriction image is deliberately not asserted. -/
def normalChainPowerMixedAnnihilator
    (hpower : ∀ n : N, (n : G) ^ p ∈ B)
    (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) :
    Submodule (ZMod p) (primeRelativeCharacters p B) :=
  normalChainPowerAnnihilator p B N hpower ⊓ normalChainMixedAnnihilator B N p hcomm

theorem normalChainRetainedCharacters_le_powerMixedAnnihilator (hBN : B ≤ N)
    (hpower : ∀ n : N, (n : G) ^ p ∈ B)
    (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) :
    normalChainRetainedCharacters B N p hBN ≤
      normalChainPowerMixedAnnihilator p B N hpower hcomm :=
  le_inf (normalChainRetainedCharacters_le_powerAnnihilator p B N hBN hpower)
    (normalChainRetainedCharacters_le_mixedAnnihilator B N p hBN hcomm)

/-- A finite test keeps every selected actual power and mixed
commutator. The lists need not generate: fewer tests give an upper bound. -/
def normalChainPowerMixedTestMap {ι κ : Type*}
    (hpower : ∀ n : N, (n : G) ^ p ∈ B)
    (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) (x : ι → N) (y : κ → G) :
    primeRelativeCharacters p B →ₗ[ZMod p] (ι ⊕ (ι × κ) → ZMod p) where
  toFun χ := Sum.elim
    (fun i => χ.1 (Additive.ofMul (normalChainPowerElement p B N hpower (x i))))
    (fun ij => χ.1 (Additive.ofMul
      (normalChainMixedCommutator B N hcomm (x ij.1) (y ij.2))))
  map_add' _ _ := by funext i; cases i <;> rfl
  map_smul' _ _ := by funext i; cases i <;> rfl

omit [N.Normal] in
theorem normalChainPowerMixedAnnihilator_le_test_ker {ι κ : Type*}
    (hpower : ∀ n : N, (n : G) ^ p ∈ B)
    (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) (x : ι → N) (y : κ → G) :
    normalChainPowerMixedAnnihilator p B N hpower hcomm ≤
      (normalChainPowerMixedTestMap p B N hpower hcomm x y).ker := by
  intro χ hχ
  apply LinearMap.mem_ker.mpr
  funext i
  cases i with
  | inl j => exact hχ.1 (x j)
  | inr jk => exact hχ.2 (x jk.1) (y jk.2)

/-- The complete original head is bounded using its actual quotient
and the same retained-character power/mixed tests. -/
theorem primeRelativeHead_chain_le_log_card_add_powerMixedTest_ker [Finite G]
    {ι κ : Type*} (hBN : B ≤ N)
    (hpower : ∀ n : N, (n : G) ^ p ∈ B)
    (hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ B) (x : ι → N) (y : κ → G) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      Nat.log p (Nat.card (normalChainQuotient B N)) +
        Module.finrank (ZMod p) (normalChainPowerMixedTestMap p B N hpower hcomm x y).ker := by
  rw [primeRelativeHead_chain_eq B N p hBN]
  apply Nat.add_le_add
  · exact (Submodule.finrank_le _).trans
      (Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
        (primeCharacters_pow_finrank_le_card p (normalChainQuotient B N)))
  · exact Submodule.finrank_mono
      ((normalChainRetainedCharacters_le_powerMixedAnnihilator p B N hBN hpower hcomm).trans
        (normalChainPowerMixedAnnihilator_le_test_ker p B N hpower hcomm x y))

/-- The intersection branch has no extra power-membership or mixed
containment inputs once the actual evaluation-kernel bound is known.
The power evaluations themselves remain in the finite test map. -/
theorem primeRelativeHead_derivedIntersection_le_log_card_add_powerMixedTest_ker
    [Finite G] {ι κ : Type*}
    (hkernel : (primeAbelianizationGroupMap p G).ker ≤ commutator G)
    (x : ι → N) (y : κ → G) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      Nat.log p (Nat.card (normalChainQuotient (N ⊓ commutator G) N)) +
        Module.finrank (ZMod p)
          (normalChainPowerMixedTestMap p (N ⊓ commutator G) N
            (normal_pow_mem_derivedIntersection_of_evaluationKernel_le p N hkernel)
            (normal_mixed_le_derivedIntersection N) x y).ker :=
  primeRelativeHead_chain_le_log_card_add_powerMixedTest_ker p (N ⊓ commutator G) N
    inf_le_left (normal_pow_mem_derivedIntersection_of_evaluationKernel_le p N hkernel)
    (normal_mixed_le_derivedIntersection N) x y

end SymmetricSubgroupAsymptotics
