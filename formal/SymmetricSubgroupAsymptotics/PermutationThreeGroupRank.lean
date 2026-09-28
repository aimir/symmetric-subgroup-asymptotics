import SymmetricSubgroupAsymptotics.PGroupPrimeIndexChain
import SymmetricSubgroupAsymptotics.TransitiveBlockQuotient
import SymmetricSubgroupAsymptotics.ImprimitiveChiefHead
import SymmetricSubgroupAsymptotics.PermutationChiefWeight
import SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit
import SymmetricSubgroupAsymptotics.PermutationTwoGroupRank
import SymmetricSubgroupAsymptotics.PGroupTransitiveDegree
import SymmetricSubgroupAsymptotics.OriginalNormalChiefHead
import SymmetricSubgroupAsymptotics.SylowEpimorphismRestriction
import Mathlib.GroupTheory.Sylow

/-!
# Ternary character rank of a finite permutation group

This file proves internally the elementary-quotient inequality needed by
the ternary permutation-kernel estimates.  It uses only finite p-group
theory and the existing original-block and induced-head infrastructure.

For a transitive 3-group, a cover of a point stabilizer gives blocks of
size three.  The literal top action has smaller degree.  The relative head
of the literal block kernel is bounded by the already proved ternary index
width on the original block set; the local component has degree three and
therefore chosen-chief ternary weight at most one.  Strong degree induction
and the existing intransitive orbit split prove the bound for every faithful
3-group action.  Restriction of characters to an actual Sylow 3-subgroup
then proves the result for an arbitrary finite faithful action.

No Kovacs--Praeger premise, transitivity premise on the final action, or
classification input occurs in the statements below.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A point-stabilizer cover in a transitive 3-group.  The upper subgroup
may be the whole group, which includes the degree-three base case. -/
structure TransitiveThreeBlockCover {X : Type}
    (U : Subgroup (Equiv.Perm X)) (x : X) where
  subgroup : Subgroup U
  covers : MulAction.stabilizer U x ⋖ subgroup
  relIndex_three : (MulAction.stabilizer U x).relIndex subgroup = 3

/-- The prime-index cover is constructed in the original subgroup lattice. -/
theorem transitiveThreeBlockCover_nonempty
    {X : Type} [Finite X] [Nontrivial X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hU : IsPGroup 3 U) (x : X) :
    Nonempty (TransitiveThreeBlockCover U x) := by
  classical
  letI : Finite (Subgroup U) :=
    Finite.of_injective (fun H : Subgroup U => (H : Set U)) SetLike.coe_injective
  letI : Fintype (Subgroup U) := Fintype.ofFinite _
  letI : LocallyFiniteOrder (Subgroup U) := Fintype.toLocallyFiniteOrder
  have hne : MulAction.stabilizer U x ≠ ⊤ := by
    intro he
    obtain ⟨y, hy⟩ := exists_ne x
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U x y
    have hx : u • x = x := by
      have hmem : u ∈ MulAction.stabilizer U x := by
        rw [he]
        exact Subgroup.mem_top u
      exact hmem
    exact hy (hu.symm.trans hx)
  obtain ⟨H, hcover, _⟩ := exists_covBy_le_of_lt (lt_top_iff_ne_top.mpr hne)
  exact ⟨⟨H, hcover, pGroup_subgroupCover_relIndex hU _ _ hcover⟩⟩

namespace TransitiveThreeBlockCover

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] {x : X}
    (D : TransitiveThreeBlockCover U x)

abbrev Points : Type := U ⧸ D.subgroup

abbrev base : D.Points := ((1 : U) : U ⧸ D.subgroup)

def map : X → D.Points := originalTransitiveBlockMap x D.subgroup

theorem map_equivariant (u : U) (y : X) :
    D.map (u • y) = u • D.map y :=
  originalTransitiveBlockMap_equivariant x D.subgroup D.covers.le u y

theorem map_base : D.map x = D.base :=
  originalTransitiveBlockMap_base x D.subgroup D.covers.le

abbrev Fibre : Type := originalBlockFibre D.map D.base

theorem fibre_card : Nat.card D.Fibre = 3 :=
  (originalTransitiveBlockFibre_card x D.subgroup D.covers.le).trans
    D.relIndex_three

abbrev topMap : U →* Equiv.Perm D.Points := MulAction.toPermHom U D.Points

abbrev Top : Subgroup (Equiv.Perm D.Points) := D.topMap.range

theorem top_pretransitive : MulAction.IsPretransitive D.Top D.Points := by
  constructor
  intro i j
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U i j
  exact ⟨D.topMap.rangeRestrict u, hu⟩

theorem top_faithful : FaithfulSMul D.Top D.Points := inferInstance

theorem top_isPGroup (hU : IsPGroup 3 U) : IsPGroup 3 D.Top :=
  hU.of_surjective D.topMap.rangeRestrict D.topMap.rangeRestrict_surjective

theorem top_finite : Finite D.Top :=
  Finite.of_surjective D.topMap.rangeRestrict D.topMap.rangeRestrict_surjective

abbrev Component : Subgroup (Equiv.Perm D.Fibre) :=
  originalBlockComponent D.map D.map_equivariant D.base

theorem component_finite : Finite D.Component :=
  Finite.of_surjective
    (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
    (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective

theorem degree_product : 3 * Nat.card D.Points = Nat.card X := by
  have h := originalTransitiveBlock_degree_product x D.subgroup D.covers.le
  change Nat.card D.Fibre * Nat.card D.Points = Nat.card X at h
  rwa [D.fibre_card] at h

theorem points_card_pos : 0 < Nat.card D.Points := Nat.card_pos

theorem points_card_lt : Nat.card D.Points < Nat.card X := by
  have hp := D.degree_product
  have hpos := D.points_card_pos
  omega

/-- The literal block kernel has at most the ternary index width of the
literal block set.  The local component has exactly three points, so its
chosen-chief ternary weight is at most one by the factorial valuation bound. -/
theorem kernel_relativeHead_le_indexWidth :
    Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 D.topMap.ker) ≤
      ternaryIndexWidth (Nat.card D.Points) := by
  letI : Finite D.Component := D.component_finite
  let c : ActualChiefSeries D.Component := actualChiefSeries D.Component
  have hc : actualChiefSeriesTernaryWeight c ≤ 1 := by
    apply permutationChiefWeight_le_one_of_card_le_five D.Component c
    rw [D.fibre_card]
    omega
  have hreal := originalBlockChiefHead_bound
    D.map D.map_equivariant D.base D.topMap.ker (by exact le_rfl) c
  have hnat : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 D.topMap.ker) ≤
        actualChiefSeriesTernaryWeight c *
          ternaryIndexWidth (Nat.card D.Points) := by
    exact_mod_cast hreal
  exact hnat.trans (by
    have h := Nat.mul_le_mul_right (ternaryIndexWidth (Nat.card D.Points)) hc
    simpa only [one_mul] using h)

end TransitiveThreeBlockCover

/-- A faithful action on a subsingleton set has no nonzero prime character. -/
theorem primeCharacterRank_eq_zero_of_subsingleton_faithful_action
    {p : ℕ} [Fact p.Prime] {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] [Subsingleton X] :
    Module.finrank (ZMod p) (PrimeCharacters p G) = 0 := by
  letI : Subsingleton G := ⟨fun a b =>
    eq_of_smul_eq_smul (α := X) (fun y => Subsingleton.elim (a • y) (b • y))⟩
  have hz (chi : PrimeCharacters p G) : chi = 0 := by
    ext g
    have hg : g = (0 : Additive G) := Subsingleton.elim _ _
    rw [hg]
    exact chi.map_zero
  letI : Subsingleton (PrimeCharacters p G) :=
    ⟨fun chi psi => (hz chi).trans (hz psi).symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- Transitive step in the degree induction for faithful 3-group actions. -/
theorem threeGroup_transitive_primeCharacterRank_le_third_of_smaller
    {X : Type} [Finite X] [Nontrivial X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hU : IsPGroup 3 U) (x : X)
    (hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup 3 H →
        Nat.card Y < Nat.card X →
        Module.finrank (ZMod 3) (PrimeCharacters 3 H) ≤ Nat.card Y / 3) :
    Module.finrank (ZMod 3) (PrimeCharacters 3 U) ≤ Nat.card X / 3 := by
  classical
  obtain ⟨D⟩ := transitiveThreeBlockCover_nonempty U hU x
  have hext : Module.finrank (ZMod 3) (PrimeCharacters 3 U) ≤
      Module.finrank (ZMod 3) (PrimeCharacters 3 D.Top) +
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 D.topMap.ker) := by
    have hdim (K L : Subgroup U) [K.Normal] [L.Normal] (h : K = L) :
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 K) =
          Module.finrank (ZMod 3) (primeRelativeCharacters 3 L) := by
      subst L
      rfl
    have hker := hdim D.topMap.rangeRestrict.ker D.topMap.ker
      (MonoidHom.ker_rangeRestrict D.topMap)
    have h := primeCharacterRank_extension_le 3 D.topMap.rangeRestrict
      D.topMap.rangeRestrict_surjective
    rwa [hker] at h
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  have htop := hsmaller D.Top D.Points (D.top_isPGroup hU) D.points_card_lt
  have hkernel := D.kernel_relativeHead_le_indexWidth
  obtain ⟨k, hk⟩ := pGroup_transitive_degree (D.top_isPGroup hU) D.base
    (fun y => MulAction.exists_smul_eq D.Top D.base y)
  by_cases hk0 : k = 0
  · have hpoints : Nat.card D.Points = 1 := by
      rw [hk, hk0, pow_zero]
    have hwidth : ternaryIndexWidth (Nat.card D.Points) = 1 := by
      rw [hpoints, ternaryIndexWidth_one]
    have hdegree := D.degree_product
    omega
  · have hpoints : 3 ≤ Nat.card D.Points := by
      rw [hk]
      have hp : (3 : ℕ) ^ 1 ≤ 3 ^ k :=
        Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) (by omega)
      simpa only [pow_one] using hp
    have hwidth := ternaryIndexWidth_le_third (Nat.card D.Points) hpoints
    have hdegree := D.degree_product
    omega

/-- Every finite faithful 3-group action satisfies the exact third-degree
bound, without a transitivity assumption. -/
theorem permutationThreeGroup_primeCharacterRank_le
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hG : IsPGroup 3 G) :
    Module.finrank (ZMod 3) (PrimeCharacters 3 G) ≤ Nat.card X / 3 := by
  classical
  have hmain : ∀ n : ℕ,
      ∀ (G₀ X₀ : Type) [Group G₀] [Finite G₀] [Finite X₀]
        [MulAction G₀ X₀] [FaithfulSMul G₀ X₀], Nat.card X₀ = n →
        IsPGroup 3 G₀ →
        Module.finrank (ZMod 3) (PrimeCharacters 3 G₀) ≤ Nat.card X₀ / 3 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G₀ X₀ _ _ _ _ _ hdegree hG₀
      have hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
          [MulAction H Y] [FaithfulSMul H Y], IsPGroup 3 H →
            Nat.card Y < Nat.card X₀ →
            Module.finrank (ZMod 3) (PrimeCharacters 3 H) ≤ Nat.card Y / 3 := by
        intro H Y _ _ _ _ _ hH hlt
        exact ih (Nat.card Y) (by omega) H Y rfl hH
      rcases subsingleton_or_nontrivial X₀ with hX | hX
      · letI : Subsingleton X₀ := hX
        rw [primeCharacterRank_eq_zero_of_subsingleton_faithful_action
          (p := 3) (X := X₀)]
        exact Nat.zero_le _
      · letI : Nontrivial X₀ := hX
        by_cases ht : MulAction.IsPretransitive G₀ X₀
        · letI : MulAction.IsPretransitive G₀ X₀ := ht
          let phi : G₀ →* Equiv.Perm X₀ := MulAction.toPermHom G₀ X₀
          let U : Subgroup (Equiv.Perm X₀) := phi.range
          let e : G₀ ≃* U := MonoidHom.ofInjective
            (show Function.Injective phi from MulAction.toPerm_injective)
          letI : MulAction.IsPretransitive U X₀ := by
            constructor
            intro x y
            obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G₀ x y
            exact ⟨phi.rangeRestrict g, hg⟩
          have hU : IsPGroup 3 U :=
            hG₀.of_surjective phi.rangeRestrict phi.rangeRestrict_surjective
          rw [primeCharacter_finrank_congr 3 e]
          exact threeGroup_transitive_primeCharacterRank_le_third_of_smaller
            U hU (Classical.choice (inferInstance : Nonempty X₀)) hsmaller
        · obtain ⟨S, hS, hC⟩ :=
            PermutationCharacterRankSplit.exists_nonempty_proper_invariant ht
          letI : FaithfulSMul
              (PermutationCharacterRankSplit.Kernel S) ↥(Sᶜ) :=
            PermutationCharacterRankSplit.kernel_complement_faithful S
          have hlt := PermutationCharacterRankSplit.degrees_lt S hS hC
          exact PermutationCharacterRankSplit.rank_le_card_div S 3
            (hsmaller (PermutationCharacterRankSplit.Image S) S
              (PermutationCharacterRankSplit.image_isPGroup S 3 hG₀) hlt.1)
            (hsmaller (PermutationCharacterRankSplit.Kernel S) ↥(Sᶜ)
              (PermutationCharacterRankSplit.kernel_isPGroup S 3 hG₀) hlt.2)
  exact hmain (Nat.card X) G X rfl hG

/-- The prime abelianization of a faithful permutation 3-group has the
same sharp one-third rank bound as its complete scalar-character space. -/
theorem permutationThreeGroup_primeAbelianizationRank_le
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hG : IsPGroup 3 G) :
    Module.finrank (ZMod 3) (PrimeAbelianization 3 G) ≤ Nat.card X / 3 := by
  simpa only [PrimeAbelianization, Subspace.dual_finrank_eq] using
    permutationThreeGroup_primeCharacterRank_le G X hG

/-- The actual Sylow 3-subgroup of the kernel of an original quotient map
inherits the sharp one-third rank bound on the unchanged source points. -/
theorem permutationThreeGroup_sylowKernel_primeAbelianizationRank_le
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) {B : Type} [Group B]
    (beta : J →* B) (P : Sylow 3 beta.ker) :
    (Module.finrank (ZMod 3)
      (PrimeAbelianization 3 (P : Subgroup beta.ker)) : ℝ) ≤ (b : ℝ) / 3 := by
  have hnat : Module.finrank (ZMod 3)
      (PrimeAbelianization 3 (P : Subgroup beta.ker)) ≤ b / 3 := by
    simpa only [Nat.card_fin] using
      permutationThreeGroup_primeAbelianizationRank_le
        (P : Subgroup beta.ker) (Fin b) P.isPGroup'
  have hthree : 3 * Module.finrank (ZMod 3)
      (PrimeAbelianization 3 (P : Subgroup beta.ker)) ≤ b := by omega
  have hreal : (3 : ℝ) * (Module.finrank (ZMod 3)
      (PrimeAbelianization 3 (P : Subgroup beta.ker)) : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hthree
  linarith

/-- Restriction of complete prime characters to an actual Sylow subgroup. -/
def primeCharacterSylowRestriction
    (p : ℕ) [Fact p.Prime] {G : Type*} [Group G]
    (P : Sylow p G) :
    PrimeCharacters p G →ₗ[ZMod p] PrimeCharacters p (P : Subgroup G) where
  toFun chi := chi.comp (P : Subgroup G).subtype.toAdditive
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A Sylow subgroup detects every prime-valued character of the original
finite group. -/
theorem primeCharacterSylowRestriction_injective
    (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (P : Sylow p G) :
    Function.Injective (primeCharacterSylowRestriction p P) := by
  have htarget : IsPGroup p (Multiplicative (ZMod p)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
      Nat.card_zmod, pow_one]
  intro chi psi h
  apply AddMonoidHom.toMultiplicativeRight.injective
  apply sylow_pGroup_hom_restriction_injective P htarget
  ext x
  exact congrArg Multiplicative.ofAdd
    (DFunLike.congr_fun h (Additive.ofMul x))

/-- The exact elementary ternary quotient rank bound for every finite
faithful permutation action. -/
theorem permutation_ternaryCharacterRank_le_third
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] :
    Module.finrank (ZMod 3) (PrimeCharacters 3 G) ≤ Nat.card X / 3 := by
  let P : Sylow 3 G := Classical.choice inferInstance
  exact ((primeCharacterSylowRestriction 3 P).finrank_le_finrank_of_injective
    (primeCharacterSylowRestriction_injective 3 P)).trans
      (permutationThreeGroup_primeCharacterRank_le (P : Subgroup G) X P.isPGroup')

/-- Restricting to a Sylow two-subgroup upgrades the internally proved
two-group theorem to every finite faithful action. -/
theorem permutation_binaryCharacterRank_le_half
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] :
    Module.finrank (ZMod 2) (PrimeCharacters 2 G) ≤ Nat.card X / 2 := by
  let P : Sylow 2 G := Classical.choice inferInstance
  exact ((primeCharacterSylowRestriction 2 P).finrank_le_finrank_of_injective
    (primeCharacterSylowRestriction_injective 2 P)).trans
      (permutationTwoGroup_primeCharacterRank_le (P : Subgroup G) X P.isPGroup')

/-- The literal kernel of the original map inherits the same faithful
action on the same original `b` labels. -/
theorem epimorphismKernel_ternaryCharacterRank_le_third
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    {B : Type*} [Group B] (beta : J →* B) :
    Module.finrank (ZMod 3) (PrimeCharacters 3 beta.ker) ≤ b / 3 := by
  simpa only [Nat.card_fin] using
    permutation_ternaryCharacterRank_le_third beta.ker (Fin b)

/-- The literal kernel of the original map also inherits the internally
proved binary half-degree bound. -/
theorem epimorphismKernel_binaryCharacterRank_le_half
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    {B : Type*} [Group B] (beta : J →* B) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 beta.ker) ≤ b / 2 := by
  simpa only [Nat.card_fin] using
    permutation_binaryCharacterRank_le_half beta.ker (Fin b)

/-- Multiplicative-budget form consumed by the fixed-source prime-base
mass estimates. -/
theorem groupEpimorphismKernel_three_mul_rank_le_degree
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    {B : Type*} [Group B] (beta : GroupEpimorphism J B) :
    3 * Module.finrank (ZMod 3) (PrimeCharacters 3 beta.1.ker) ≤ b := by
  have h := epimorphismKernel_ternaryCharacterRank_le_third J beta.1
  omega

/-- Binary consumer form, with no external permutation-quotient premise. -/
theorem groupEpimorphismKernel_two_mul_rank_le_degree
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    {B : Type*} [Group B] (beta : GroupEpimorphism J B) :
    2 * Module.finrank (ZMod 2) (PrimeCharacters 2 beta.1.ker) ≤ b := by
  have h := epimorphismKernel_binaryCharacterRank_le_half J beta.1
  omega

end SymmetricSubgroupAsymptotics

end
