import SymmetricSubgroupAsymptotics.PrimeTranslationFrame
import SymmetricSubgroupAsymptotics.PermutationThreeGroupRank

/-!
# The elementary `p`-quotient rank of a permutation group, for every prime

For every prime `p` and every finite faithful permutation action of a group
`G` on `X`,

`d_p(G) = dim Hom(G, ZMod p) ≤ |X| / p`.

The proof is internal, by strong induction on the degree, as for `p = 2, 3`.
A transitive `p`-group `U` has a central element `z` of order `p`.  Since `U`
is transitive, `z` is fixed-point-free, its orbits are blocks of size `p`,
and because `z` is central every element of `U` acts on these blocks by
translations in the coordinates `x ↦ zᵃ x`.  The block kernel is therefore a
subrepresentation of the permutation module on the blocks, whose head is at
most `|I| / p`; the top acts on `|I| = |X| / p` blocks.  Restriction to a
Sylow subgroup gives the bound for every finite group.

No Kovács–Praeger premise, classification, or finite catalogue is used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace CentralPrimeFrame

open Equiv

variable {p : ℕ} [hp : Fact p.Prime] {X : Type} [Finite X] (U : Subgroup (Perm X))

/-- A transitive nontrivial `p`-group has a central element of order `p`. -/
theorem exists_central_order (hU : IsPGroup p U) (hnt : Nontrivial U) :
    ∃ z : U, z ∈ Subgroup.center U ∧ orderOf z = p := by
  haveI : Finite U := inferInstance
  haveI : Nontrivial (Subgroup.center U) := hU.center_nontrivial
  have hcen : IsPGroup p (Subgroup.center U) := hU.to_subgroup _
  obtain ⟨n, hn, hcard⟩ := hcen.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card (Subgroup.center U) := by
    rw [hcard]
    exact dvd_pow_self p (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩

variable {U} [MulAction.IsPretransitive U X]
variable (z : U) (hz : z ∈ Subgroup.center U) (hzp : orderOf z = p)

/-- The central permutation. -/
abbrev σ : Perm X := (z : Perm X)

omit [Finite X] [MulAction.IsPretransitive U X] in
include hz in
theorem commute_σ (u : U) : (u : Perm X) * σ z = σ z * u := by
  have := Subgroup.mem_center_iff.mp hz u
  exact congrArg Subtype.val this

omit [Finite X] [MulAction.IsPretransitive U X] in
include hz in
theorem commute_σ_zpow (u : U) (n : ℤ) : (u : Perm X) * σ z ^ n = σ z ^ n * u :=
  (Commute.zpow_right (commute_σ z hz u) n)

include hz in
omit [Finite X] in
/-- A power of the central permutation with a fixed point is trivial. -/
theorem zpow_eq_one_of_fixed (n : ℤ) (x : X) (hx : (σ z ^ n) x = x) : σ z ^ n = 1 := by
  ext y
  obtain ⟨u, rfl⟩ := MulAction.exists_smul_eq U x y
  change (σ z ^ n) ((u : Perm X) x) = (u : Perm X) x
  have := congrArg (fun π : Perm X => π x) (commute_σ_zpow z hz u n)
  simp only [Perm.mul_apply] at this
  rw [← this, hx]

omit hp [Finite X] [MulAction.IsPretransitive U X] in
include hzp in
theorem orderOf_σ : orderOf (σ z) = p := by
  rw [Subgroup.orderOf_coe, hzp]

/-- The blocks: orbits of the central permutation. -/
abbrev Blocks := MulAction.orbitRel.Quotient (Subgroup.zpowers (σ z)) X

omit [Finite X] [MulAction.IsPretransitive U X] in
theorem mem_orbit_zpow (x : X) (n : ℤ) :
    (σ z ^ n) x ∈ MulAction.orbit (Subgroup.zpowers (σ z)) x :=
  ⟨⟨σ z ^ n, n, rfl⟩, rfl⟩

omit [Finite X] [MulAction.IsPretransitive U X] in
theorem mk_zpow (x : X) (n : ℤ) :
    (⟦(σ z ^ n) x⟧ : Blocks z) = ⟦x⟧ :=
  Quotient.sound (mem_orbit_zpow z x n)

omit [Finite X] [MulAction.IsPretransitive U X] in
theorem mk_pow (x : X) (n : ℕ) : (⟦(σ z ^ n) x⟧ : Blocks z) = ⟦x⟧ := by
  have := mk_zpow z x (n : ℤ)
  rwa [zpow_natCast] at this

include hz in
/-- The top action on the blocks. -/
def topFun (u : U) : Blocks z → Blocks z :=
  Quotient.map' (fun x => (u : Perm X) x) (by
    rintro a b ⟨⟨h, n, rfl⟩, hab⟩
    refine ⟨⟨σ z ^ n, n, rfl⟩, ?_⟩
    change (σ z ^ n) ((u : Perm X) b) = (u : Perm X) a
    rw [← hab]
    change (σ z ^ n) ((u : Perm X) b) = (u : Perm X) ((σ z ^ n) b)
    have := congrArg (fun π : Perm X => π b) (commute_σ_zpow z hz u n)
    simp only [Perm.mul_apply] at this
    exact this.symm)

omit [Finite X] [MulAction.IsPretransitive U X] in
theorem topFun_mk (u : U) (x : X) : topFun z hz u ⟦x⟧ = ⟦(u : Perm X) x⟧ := rfl

omit [Finite X] [MulAction.IsPretransitive U X] in
include hz in
theorem topFun_mul (u v : U) (i : Blocks z) :
    topFun z hz (u * v) i = topFun z hz u (topFun z hz v i) := by
  induction i using Quotient.inductionOn with
  | h x => rfl

include hz in
omit [Finite X] [MulAction.IsPretransitive U X] in
theorem topFun_one (i : Blocks z) : topFun z hz 1 i = i := by
  induction i using Quotient.inductionOn with
  | h x => rfl

/-- The top action on the blocks as a homomorphism. -/
def topHom : U →* Perm (Blocks z) where
  toFun u :=
    { toFun := topFun z hz u
      invFun := topFun z hz u⁻¹
      left_inv := fun i => by rw [← topFun_mul, inv_mul_cancel, topFun_one]
      right_inv := fun i => by rw [← topFun_mul, mul_inv_cancel, topFun_one] }
  map_one' := by
    refine Equiv.ext fun i => ?_
    exact topFun_one z hz i
  map_mul' u v := by
    refine Equiv.ext fun i => ?_
    exact topFun_mul z hz u v i

omit [Finite X] [MulAction.IsPretransitive U X] in
theorem topHom_apply (u : U) (i : Blocks z) : topHom z hz u i = topFun z hz u i := rfl

theorem topHom_transitive (i j : Blocks z) : ∃ u : U, topHom z hz u i = j := by
  induction i using Quotient.inductionOn with
  | h x =>
    induction j using Quotient.inductionOn with
    | h y =>
      obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U x y
      exact ⟨u, by rw [topHom_apply, topFun_mk]; exact congrArg _ hu⟩

/-- The frame map `(i, a) ↦ zᵃ · rep(i)`. -/
def frameFun (q : Blocks z × ZMod p) : X := (σ z ^ q.2.val) (Quotient.out q.1)

include hzp in
omit [Finite X] [MulAction.IsPretransitive U X] in
theorem zpow_eq_pow_val (n : ℤ) : σ z ^ n = σ z ^ ((n : ZMod p).val) := by
  rw [← zpow_natCast, ZMod.val_intCast]
  have hp0 : (p : ℤ) = (orderOf (σ z) : ℤ) := by rw [orderOf_σ z hzp]
  rw [hp0, zpow_mod_orderOf]

include hz hzp in
omit [Finite X] in
theorem frameFun_bijective : Function.Bijective (frameFun (p := p) z) := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := by
      have := congrArg (fun x => (⟦x⟧ : Blocks z)) h
      simp only [frameFun, mk_pow, Quotient.out_eq] at this
      exact this
    subst hij
    have h' : (σ z ^ a.val) (Quotient.out i) = (σ z ^ b.val) (Quotient.out i) := h
    have hfix : (σ z ^ ((b.val : ℤ) - a.val)) ((σ z ^ a.val) (Quotient.out i)) =
        (σ z ^ a.val) (Quotient.out i) := by
      rw [← Perm.mul_apply, ← zpow_natCast (σ z) a.val, ← zpow_add, sub_add_cancel,
        zpow_natCast]
      exact h'.symm
    have h1 := zpow_eq_one_of_fixed z hz _ _ hfix
    have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [orderOf_σ z hzp] at hdvd
    have hab : ((b.val : ℤ) : ZMod p) = ((a.val : ℤ) : ZMod p) := by
      rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hdvd
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hab
    rw [hab]
  · intro x
    have hout : Quotient.out (⟦x⟧ : Blocks z) ∈ MulAction.orbit (Subgroup.zpowers (σ z)) x :=
      Quotient.mk_out (s := MulAction.orbitRel (Subgroup.zpowers (σ z)) X) x
    obtain ⟨⟨h, n, rfl⟩, hn⟩ := hout
    refine ⟨(⟦x⟧, ((-n : ℤ) : ZMod p)), ?_⟩
    change (σ z ^ (((-n : ℤ) : ZMod p).val)) (Quotient.out (⟦x⟧ : Blocks z)) = x
    rw [← zpow_eq_pow_val z hzp]
    have hn' : (σ z ^ n) x = Quotient.out (⟦x⟧ : Blocks z) := hn
    rw [← hn', ← Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Perm.one_apply]

/-- The block frame. -/
def frame : Blocks z × ZMod p ≃ X := Equiv.ofBijective _ (frameFun_bijective z hz hzp)

theorem frame_apply (q : Blocks z × ZMod p) :
    frame z hz hzp q = (σ z ^ q.2.val) (Quotient.out q.1) := rfl

theorem frame_symm_fst (x : X) : ((frame z hz hzp).symm x).1 = ⟦x⟧ := by
  conv_rhs => rw [← (frame z hz hzp).apply_symm_apply x]
  rw [frame_apply, mk_pow, Quotient.out_eq]

include hzp in
theorem frame_add (j : Blocks z) (c a : ZMod p) :
    frame z hz hzp (j, c + a) = (σ z ^ a.val) (frame z hz hzp (j, c)) := by
  rw [frame_apply, frame_apply, ← Perm.mul_apply, ← pow_add]
  congr 1
  have h1 := zpow_eq_pow_val z hzp ((a.val + c.val : ℕ) : ℤ)
  rw [zpow_natCast] at h1
  rw [h1]
  congr 2
  push_cast
  simp [add_comm]

/-- The prime translation frame of the central permutation. -/
def translationFrame : PrimeTranslationFrame p U (Blocks z) where
  frame := frame z hz hzp
  top := topHom z hz
  intertwine u q := by
    rw [frame_symm_fst, frame_apply, topHom_apply]
    change (⟦(u : Perm X) ((σ z ^ q.2.val) (Quotient.out q.1))⟧ : Blocks z) =
      topFun z hz u q.1
    have := congrArg (fun π : Perm X => π (Quotient.out q.1))
      (commute_σ_zpow z hz u (q.2.val : ℤ))
    simp only [Perm.mul_apply, zpow_natCast] at this
    rw [this, mk_pow]
    conv_rhs => rw [← Quotient.out_eq q.1]
    exact (topFun_mk z hz u _).symm
  translate u i a := by
    have h0 : frame z hz hzp (i, a) = (σ z ^ a.val) (frame z hz hzp (i, 0)) := by
      rw [← frame_add z hz hzp, zero_add]
    have hc : (u : Perm X) ((σ z ^ a.val) (frame z hz hzp (i, 0))) =
        (σ z ^ a.val) ((u : Perm X) (frame z hz hzp (i, 0))) := by
      have := congrArg (fun π : Perm X => π (frame z hz hzp (i, 0)))
        (commute_σ_zpow z hz u (a.val : ℤ))
      simpa only [Perm.mul_apply, zpow_natCast] using this
    rw [h0, hc]
    set q := (frame z hz hzp).symm ((u : Perm X) (frame z hz hzp (i, 0)))
    have hq : (u : Perm X) (frame z hz hzp (i, 0)) = frame z hz hzp q :=
      ((frame z hz hzp).apply_symm_apply _).symm
    rw [hq, ← frame_add z hz hzp, (frame z hz hzp).symm_apply_apply, add_comm]

include hz hzp in
theorem card_blocks : p * Nat.card (Blocks z) = Nat.card X := by
  rw [← Nat.card_congr (frame z hz hzp), Nat.card_prod, Nat.card_zmod, mul_comm]

end CentralPrimeFrame

open Equiv

/-- The transitive step of the degree induction for a prime `p`. -/
theorem pGroup_transitive_primeCharacterRank_le_of_smaller
    (p : ℕ) [Fact p.Prime]
    {X : Type} [Finite X] [Nontrivial X]
    (U : Subgroup (Perm X)) [MulAction.IsPretransitive U X]
    (hU : IsPGroup p U)
    (hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup p H → Nat.card Y < Nat.card X →
        Module.finrank (ZMod p) (PrimeCharacters p H) ≤ Nat.card Y / p) :
    Module.finrank (ZMod p) (PrimeCharacters p U) ≤ Nat.card X / p := by
  classical
  have hpp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hnt : Nontrivial U := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U x y
    refine ⟨⟨u, 1, fun h => hxy ?_⟩⟩
    rw [← hu, h, one_smul]
  obtain ⟨z, hz, hzp⟩ := CentralPrimeFrame.exists_central_order U hU hnt
  let F := CentralPrimeFrame.translationFrame z hz hzp
  letI : MulAction U (CentralPrimeFrame.Blocks z) :=
    MulAction.compHom _ (CentralPrimeFrame.topHom z hz)
  have hact : ∀ (u : U) (i : CentralPrimeFrame.Blocks z), u • i = F.top u i := fun _ _ => rfl
  have hext : Module.finrank (ZMod p) (PrimeCharacters p U) ≤
      Module.finrank (ZMod p) (PrimeCharacters p F.top.range) +
        Module.finrank (ZMod p) (primeRelativeCharacters p F.top.ker) := by
    have hdim (K L : Subgroup U) [K.Normal] [L.Normal] (h : K = L) :
        Module.finrank (ZMod p) (primeRelativeCharacters p K) =
          Module.finrank (ZMod p) (primeRelativeCharacters p L) := by
      subst L
      rfl
    have hker := hdim F.top.rangeRestrict.ker F.top.ker (MonoidHom.ker_rangeRestrict F.top)
    have h := primeCharacterRank_extension_le p F.top.rangeRestrict
      F.top.rangeRestrict_surjective
    rw [hker] at h
    exact h
  have hcard := CentralPrimeFrame.card_blocks z hz hzp
  have hdeg : Nat.card X / p = Nat.card (CentralPrimeFrame.Blocks z) := by
    rw [← hcard, Nat.mul_div_cancel_left _ (by omega)]
  haveI : Finite (CentralPrimeFrame.Blocks z) := inferInstance
  haveI : Nonempty (CentralPrimeFrame.Blocks z) :=
    ⟨⟦Classical.choice (inferInstance : Nonempty X)⟧⟩
  have hpos : 0 < Nat.card (CentralPrimeFrame.Blocks z) := Nat.card_pos
  rcases subsingleton_or_nontrivial (CentralPrimeFrame.Blocks z) with hI | hI
  · letI : Subsingleton (CentralPrimeFrame.Blocks z) := hI
    have htop : Module.finrank (ZMod p) (PrimeCharacters p F.top.range) = 0 :=
      primeCharacterRank_eq_zero_of_subsingleton_action (X := CentralPrimeFrame.Blocks z)
    have hkernel := F.kernel_relativeHead_le_card hact
    omega
  · letI : Nontrivial (CentralPrimeFrame.Blocks z) := hI
    letI : MulAction.IsPretransitive U (CentralPrimeFrame.Blocks z) :=
      ⟨fun i j => CentralPrimeFrame.topHom_transitive z hz i j⟩
    letI : MulAction.IsPretransitive F.top.range (CentralPrimeFrame.Blocks z) := by
      constructor
      intro i j
      obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U i j
      exact ⟨F.top.rangeRestrict u, hu⟩
    have hTop : IsPGroup p F.top.range :=
      hU.of_surjective F.top.rangeRestrict F.top.rangeRestrict_surjective
    letI : Finite F.top.range := Finite.of_surjective F.top.rangeRestrict
      F.top.rangeRestrict_surjective
    have hlt : Nat.card (CentralPrimeFrame.Blocks z) < Nat.card X := by
      rw [← hcard]
      nlinarith
    have htop := hsmaller F.top.range (CentralPrimeFrame.Blocks z) hTop hlt
    have hkernel := F.kernel_relativeHead_le_div hact hU
    have h2 : 2 * (Nat.card (CentralPrimeFrame.Blocks z) / p) ≤
        Nat.card (CentralPrimeFrame.Blocks z) := by
      calc 2 * (Nat.card (CentralPrimeFrame.Blocks z) / p)
          ≤ p * (Nat.card (CentralPrimeFrame.Blocks z) / p) := Nat.mul_le_mul_right _ hpp
        _ ≤ Nat.card (CentralPrimeFrame.Blocks z) := Nat.mul_div_le _ _
    omega

/-- Every finite faithful `p`-group action satisfies `d_p ≤ degree / p`. -/
theorem permutationPGroup_primeCharacterRank_le (p : ℕ) [Fact p.Prime]
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hG : IsPGroup p G) :
    Module.finrank (ZMod p) (PrimeCharacters p G) ≤ Nat.card X / p := by
  classical
  have hmain : ∀ n : ℕ,
      ∀ (G₀ X₀ : Type) [Group G₀] [Finite G₀] [Finite X₀]
        [MulAction G₀ X₀] [FaithfulSMul G₀ X₀], Nat.card X₀ = n →
        IsPGroup p G₀ →
        Module.finrank (ZMod p) (PrimeCharacters p G₀) ≤ Nat.card X₀ / p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G₀ X₀ _ _ _ _ _ hdegree hG₀
      have hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
          [MulAction H Y] [FaithfulSMul H Y], IsPGroup p H →
            Nat.card Y < Nat.card X₀ →
            Module.finrank (ZMod p) (PrimeCharacters p H) ≤ Nat.card Y / p := by
        intro H Y _ _ _ _ _ hH hlt
        exact ih (Nat.card Y) (by omega) H Y rfl hH
      rcases subsingleton_or_nontrivial X₀ with hX | hX
      · letI : Subsingleton X₀ := hX
        rw [primeCharacterRank_eq_zero_of_subsingleton_faithful_action (p := p) (X := X₀)]
        exact Nat.zero_le _
      · letI : Nontrivial X₀ := hX
        by_cases ht : MulAction.IsPretransitive G₀ X₀
        · letI : MulAction.IsPretransitive G₀ X₀ := ht
          let phi : G₀ →* Perm X₀ := MulAction.toPermHom G₀ X₀
          let U : Subgroup (Perm X₀) := phi.range
          let e : G₀ ≃* U := MonoidHom.ofInjective
            (show Function.Injective phi from MulAction.toPerm_injective)
          letI : MulAction.IsPretransitive U X₀ := by
            constructor
            intro x y
            obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G₀ x y
            exact ⟨phi.rangeRestrict g, hg⟩
          have hU : IsPGroup p U :=
            hG₀.of_surjective phi.rangeRestrict phi.rangeRestrict_surjective
          rw [primeCharacter_finrank_congr p e]
          exact pGroup_transitive_primeCharacterRank_le_of_smaller p U hU hsmaller
        · obtain ⟨S, hS, hC⟩ :=
            PermutationCharacterRankSplit.exists_nonempty_proper_invariant ht
          letI : FaithfulSMul
              (PermutationCharacterRankSplit.Kernel S) ↥(Sᶜ) :=
            PermutationCharacterRankSplit.kernel_complement_faithful S
          have hlt := PermutationCharacterRankSplit.degrees_lt S hS hC
          exact PermutationCharacterRankSplit.rank_le_card_div S p
            (hsmaller (PermutationCharacterRankSplit.Image S) S
              (PermutationCharacterRankSplit.image_isPGroup S p hG₀) hlt.1)
            (hsmaller (PermutationCharacterRankSplit.Kernel S) ↥(Sᶜ)
              (PermutationCharacterRankSplit.kernel_isPGroup S p hG₀) hlt.2)
  exact hmain (Nat.card X) G X rfl hG

/-- **The prime-rank bound.**  For every prime `p` and every finite faithful
permutation action, `d_p(G) ≤ |X| / p`. -/
theorem permutation_primeCharacterRank_le (p : ℕ) [Fact p.Prime]
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] :
    Module.finrank (ZMod p) (PrimeCharacters p G) ≤ Nat.card X / p := by
  let P : Sylow p G := Classical.choice inferInstance
  exact ((primeCharacterSylowRestriction p P).finrank_le_finrank_of_injective
    (primeCharacterSylowRestriction_injective p P)).trans
      (permutationPGroup_primeCharacterRank_le p (P : Subgroup G) X P.isPGroup')

/-- Every subgroup of an actual source `J ≤ S_b` has `d_p ≤ b / p`. -/
theorem primeRank_le_of_subgroup (p : ℕ) [Fact p.Prime] {b : ℕ}
    (J : Subgroup (Perm (Fin b))) (F : Subgroup J) :
    Module.finrank (ZMod p) (PrimeCharacters p F) ≤ b / p := by
  simpa only [Nat.card_fin] using permutation_primeCharacterRank_le p F (Fin b)

end SymmetricSubgroupAsymptotics
