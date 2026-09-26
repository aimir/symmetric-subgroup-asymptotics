import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame
import SymmetricSubgroupAsymptotics.BinaryPairKernelHead
import SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit

/-! The binary prime-character rank of every faithful finite 2-group
permutation action is at most half its degree. Strong degree induction uses
the original restriction image and complementary kernel in the intransitive
case, and the original correlated pair kernel in the transitive case.
No published permutation-generator bound or finite catalogue is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- A faithful action on zero or one point has no nonzero scalar character. -/
theorem primeCharacterRank_eq_zero_of_subsingleton_action
    {p : ℕ} [Fact p.Prime] {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] [Subsingleton X] :
    Module.finrank (ZMod p) (PrimeCharacters p G)=0 := by
  letI : Subsingleton G := ⟨fun a b =>
    eq_of_smul_eq_smul (α := X) (fun x => Subsingleton.elim (a • x) (b • x))⟩
  have hz (χ : PrimeCharacters p G) : χ=0 := by
    ext g
    have hg : g=(0 : Additive G) := Subsingleton.elim _ _
    rw [hg]
    exact χ.map_zero
  letI : Subsingleton (PrimeCharacters p G) :=
    ⟨fun χ ψ => (hz χ).trans (hz ψ).symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- The transitive induction step retains the exact original kernel and
uses the faithful literal top image only for the smaller-action induction.
A singleton pair-label set uses the coarse kernel bound and trivial top. -/
theorem twoGroup_transitive_primeCharacterRank_le_half_of_smaller
    {X : Type} [Finite X] [Nontrivial X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hU : IsPGroup 2 U) (x : X)
    (hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y<Nat.card X →
        Module.finrank (ZMod 2) (PrimeCharacters 2 H)≤Nat.card Y/2) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 U)≤Nat.card X/2 := by
  classical
  obtain ⟨D⟩ := transitiveBinaryPairCover_nonempty U hU x
  have hact : ∀ (u : U) (i : D.Points), u • i=D.frame.top u i := fun _ _ => rfl
  have hext : Module.finrank (ZMod 2) (PrimeCharacters 2 U)≤
      Module.finrank (ZMod 2) (PrimeCharacters 2 D.Top)+
        Module.finrank (ZMod 2) (primeRelativeCharacters 2 D.frame.top.ker) := by
    have hdim (K L : Subgroup U) [K.Normal] [L.Normal] (h : K=L) :
        Module.finrank (ZMod 2) (primeRelativeCharacters 2 K)=
          Module.finrank (ZMod 2) (primeRelativeCharacters 2 L) := by
      subst L
      rfl
    have hker := hdim D.frame.top.rangeRestrict.ker D.frame.top.ker
      (MonoidHom.ker_rangeRestrict D.frame.top)
    have h := primeCharacterRank_extension_le 2 D.frame.top.rangeRestrict
      D.frame.top.rangeRestrict_surjective
    rw [hker] at h
    exact h
  have hdegree : Nat.card X/2=Nat.card D.Points := by
    rw [← D.degree_product]
    omega
  rcases subsingleton_or_nontrivial D.Points with hI | hI
  · letI : Subsingleton D.Points := hI
    have htop : Module.finrank (ZMod 2) (PrimeCharacters 2 D.Top)=0 :=
      primeCharacterRank_eq_zero_of_subsingleton_action (X := D.Points)
    have hkernel := D.frame.kernel_relativeHead_le_card hact
    omega
  · letI : Nontrivial D.Points := hI
    have htop := hsmaller D.Top D.Points (D.top_isPGroup hU) D.points_card_lt
    have hkernel := D.frame.kernel_relativeHead_le_half hact hU
    omega

/-- All finite faithful actual actions are quantified in the induction
hypothesis, so the faithful complementary kernel is eligible unchanged. -/
theorem permutationTwoGroup_primeCharacterRank_le
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hG : IsPGroup 2 G) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 G)≤Nat.card X/2 := by
  classical
  have hmain : ∀ n : ℕ, ∀ (G₀ X₀ : Type) [Group G₀] [Finite G₀] [Finite X₀]
      [MulAction G₀ X₀] [FaithfulSMul G₀ X₀], Nat.card X₀=n → IsPGroup 2 G₀ →
        Module.finrank (ZMod 2) (PrimeCharacters 2 G₀)≤Nat.card X₀/2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G₀ X₀ _ _ _ _ _ hdegree hG₀
      have hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
          [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y<Nat.card X₀ →
            Module.finrank (ZMod 2) (PrimeCharacters 2 H)≤Nat.card Y/2 := by
        intro H Y _ _ _ _ _ hH hlt
        exact ih (Nat.card Y) (by omega) H Y rfl hH
      rcases subsingleton_or_nontrivial X₀ with hX | hX
      · letI : Subsingleton X₀ := hX
        rw [primeCharacterRank_eq_zero_of_subsingleton_action (X := X₀)]
        exact Nat.zero_le _
      · letI : Nontrivial X₀ := hX
        by_cases ht : MulAction.IsPretransitive G₀ X₀
        · letI : MulAction.IsPretransitive G₀ X₀ := ht
          let φ : G₀ →* Equiv.Perm X₀ := MulAction.toPermHom G₀ X₀
          let U : Subgroup (Equiv.Perm X₀) := φ.range
          let e : G₀ ≃* U := MonoidHom.ofInjective
            (show Function.Injective φ from MulAction.toPerm_injective)
          letI : MulAction.IsPretransitive U X₀ := by
            constructor
            intro x y
            obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G₀ x y
            exact ⟨φ.rangeRestrict g, hg⟩
          have hU : IsPGroup 2 U :=
            hG₀.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
          rw [primeCharacter_finrank_congr 2 e]
          exact twoGroup_transitive_primeCharacterRank_le_half_of_smaller U hU
            (Classical.choice (inferInstance : Nonempty X₀)) hsmaller
        · exact PermutationCharacterRankSplit.binary_rank_le_half_of_intransitive
            hG₀ ht hsmaller
  exact hmain (Nat.card X) G X rfl hG

/-- The prime abelianization is the dual of the complete scalar-character
space of the same original group. -/
theorem permutationTwoGroup_primeAbelianizationRank_le
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hG : IsPGroup 2 G) :
    Module.finrank (ZMod 2) (PrimeAbelianization 2 G)≤Nat.card X/2 := by
  simpa only [PrimeAbelianization, Subspace.dual_finrank_eq] using
    permutationTwoGroup_primeCharacterRank_le G X hG

/-- In particular, every literal permutation 2-subgroup has the sharp
half-degree bound, with no transitivity hypothesis. -/
theorem permutationTwoGroup_literal_primeAbelianizationRank_le
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X)) (hU : IsPGroup 2 U) :
    Module.finrank (ZMod 2) (PrimeAbelianization 2 U)≤Nat.card X/2 :=
  permutationTwoGroup_primeAbelianizationRank_le U X hU

/-- The numerical rank input needed by the binary Schur envelope, now on
the actual Sylow subgroup of the kernel of each original quotient map.
Its faithful action is inherited through the unchanged subtype inclusions. -/
theorem permutationTwoGroup_sylowKernel_primeAbelianizationRank_le
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) {B : Type} [Group B]
    (β : J →* B) (P : Sylow 2 β.ker) :
    (Module.finrank (ZMod 2)
      (PrimeAbelianization 2 (P : Subgroup β.ker)) : ℝ)≤(b : ℝ)/2 := by
  have hnat : Module.finrank (ZMod 2)
      (PrimeAbelianization 2 (P : Subgroup β.ker))≤b/2 := by
    simpa only [Nat.card_fin] using
      permutationTwoGroup_primeAbelianizationRank_le
        (P : Subgroup β.ker) (Fin b) P.isPGroup'
  have htwice : 2*Module.finrank (ZMod 2)
      (PrimeAbelianization 2 (P : Subgroup β.ker))≤b := by omega
  have hreal : (2 : ℝ)*(Module.finrank (ZMod 2)
      (PrimeAbelianization 2 (P : Subgroup β.ker)) : ℝ)≤(b : ℝ) := by
    exact_mod_cast htwice
  linarith

end SymmetricSubgroupAsymptotics
