import SymmetricSubgroupAsymptotics.DegreeSixBinaryBlockCoordinates
import SymmetricSubgroupAsymptotics.DegreeSixOddIndexEpiBound
import SymmetricSubgroupAsymptotics.DegreeSixBinaryBlockOwner

/-!
# Every quotient of a degree-six binary-block owner

The two-by-three binary-block owner has an index-three block kernel charted
faithfully in `F₂^3`, and an element over a three-cycle of the blocks shifts
that chart cyclically.  For every original normal subgroup `N`, write `A`
for the image of the block kernel in `G/N`.

If the shift still acts nontrivially on `A`, one binary coordinate label
detects `A` together with its two shifts, and the coprime labelling lemma
bounds the onto maps by the binary characters of the source.  If the shift
acts trivially, the coordinate sum shows that `A` has order at most two, the
quotient is abelian with a sixfold embedding, and the Kovács--Praeger input
applies.  No quotient is classified.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A homomorphism vanishing on the kernel of `ψ` descends to its range. -/
theorem exists_rangeLift_of_ker {K Q M : Type*} [Group K] [Group Q] [Group M]
    (ψ : K →* Q) (ι : K →* M) (h : ∀ k, ψ k = 1 → ι k = 1) :
    ∃ ι' : ψ.range →* M, ∀ k, ι' (ψ.rangeRestrict k) = ι k := by
  have hker : ψ.ker ≤ ι.ker := fun k hk =>
    MonoidHom.mem_ker.mpr (h k (MonoidHom.mem_ker.mp hk))
  refine ⟨(QuotientGroup.lift ψ.ker ι hker).comp
    (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom, fun k => ?_⟩
  have hk : (QuotientGroup.quotientKerEquivRange ψ).symm (ψ.rangeRestrict k) =
      (QuotientGroup.mk k : K ⧸ ψ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hk]
  rfl

/-- The binary label count in the degree-six exponent. -/
theorem binaryLabel_real_bound {Q : Type*} [Group Q] (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (h : Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (PrimeCharacters 2 (commPowSubgroup J 3)) * Nat.card (Q ≃* Q)) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      Nat.card (Q ≃* Q) * (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hc : Nat.card (PrimeCharacters 2 (commPowSubgroup J 3)) ≤ 2 ^ (b / 2) :=
    primeCharacters_commPow_card_le (p := 2) (q := 3) b J 2
      (fun G X _ _ _ _ _ => permutation_binaryCharacterRank_le_half G X)
  have hpow : (2 : ℝ) ^ (b / 2) ≤ (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h1 : ((b / 2 : ℕ) : ℝ) ≤ (b : ℝ) / 2 := Nat.cast_div_le
    have h2 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    linarith
  calc (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (Nat.card (PrimeCharacters 2 (commPowSubgroup J 3)) : ℝ) * Nat.card (Q ≃* Q) := by
        exact_mod_cast h
    _ ≤ (2 : ℝ) ^ (b / 2) * Nat.card (Q ≃* Q) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast hc
    _ ≤ (2 : ℝ) ^ ((8 / 15 : ℝ) * b) * Nat.card (Q ≃* Q) :=
        mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

/-- The group-theoretic content of the two-by-three binary-block owner: an
index-three normal block kernel charted faithfully in `F₂^3`, and an element
over a three-cycle of the blocks that shifts the chart cyclically. -/
structure BinaryBlockCoordinates (G : Type*) [Group G] where
  kernel : Subgroup G
  normal : kernel.Normal
  index_three : Nat.card (G ⧸ kernel) = 3
  chart : kernel →* Multiplicative (Fin 3 → ZMod 2)
  chart_injective : Function.Injective chart
  shift : G
  shift_not_mem : shift ∉ kernel
  chart_conj : ∀ (k : kernel) (i : Fin 3),
    (chart (letI := normal; MulAut.conjNormal shift k)).toAdd i =
      (chart k).toAdd (rotThree i)

namespace BinaryBlockCoordinates

variable {G : Type*} [Group G]

instance kernel_normal (B : BinaryBlockCoordinates G) : B.kernel.Normal := B.normal

theorem kernel_comm (B : BinaryBlockCoordinates G) (a b : B.kernel) : a * b = b * a :=
  B.chart_injective (by rw [map_mul, map_mul, mul_comm])

theorem kernel_sq (B : BinaryBlockCoordinates G) (a : B.kernel) : a ^ 2 = 1 := by
  apply B.chart_injective
  rw [map_pow, map_one, pow_two]
  exact binaryThree_add_self (B.chart a).toAdd

theorem chart_conj_conj (B : BinaryBlockCoordinates G) (k : B.kernel) (i : Fin 3) :
    (B.chart (MulAut.conjNormal B.shift (MulAut.conjNormal B.shift k))).toAdd i =
      (B.chart k).toAdd (rotThree (rotThree i)) := by
  rw [B.chart_conj, B.chart_conj]

theorem cube_mem [Finite G] (B : BinaryBlockCoordinates G) (g : G) : g ^ 3 ∈ B.kernel := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  have h := pow_card_eq_one' (G := G ⧸ B.kernel) (x := (g : G ⧸ B.kernel))
  rwa [B.index_three] at h

/-- Every element is a power of the shift times a block-kernel element. -/
theorem exists_zpow_mul [Finite G] (B : BinaryBlockCoordinates G) (g : G) :
    ∃ z : ℤ, ∃ k ∈ B.kernel, g = B.shift ^ z * k := by
  haveI : Fact (Nat.card (G ⧸ B.kernel)).Prime := ⟨by rw [B.index_three]; norm_num⟩
  have hne : Subgroup.zpowers (QuotientGroup.mk B.shift : G ⧸ B.kernel) ≠ ⊥ := by
    intro h
    apply B.shift_not_mem
    rw [← QuotientGroup.eq_one_iff]
    have hmem : (QuotientGroup.mk B.shift : G ⧸ B.kernel) ∈
        Subgroup.zpowers (QuotientGroup.mk B.shift : G ⧸ B.kernel) :=
      Subgroup.mem_zpowers _
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  have htop := (Subgroup.eq_bot_or_eq_top_of_prime_card
    (Subgroup.zpowers (QuotientGroup.mk B.shift : G ⧸ B.kernel))).resolve_left hne
  have hg : (QuotientGroup.mk g : G ⧸ B.kernel) ∈
      Subgroup.zpowers (QuotientGroup.mk B.shift : G ⧸ B.kernel) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨z, (B.shift ^ z)⁻¹ * g, ?_, (mul_inv_cancel_left _ _).symm⟩
  rw [← QuotientGroup.eq, QuotientGroup.mk_zpow]
  exact hz

section Quotient

variable (B : BinaryBlockCoordinates G) (N : Subgroup G) [N.Normal]

/-- The block kernel mapped into one literal quotient. -/
def quotChart : B.kernel →* G ⧸ N :=
  (QuotientGroup.mk' N).comp B.kernel.subtype

/-- The image of the block kernel in one literal quotient. -/
abbrev quotBase : Subgroup (G ⧸ N) := (B.quotChart N).range

theorem quotBase_eq_map : B.quotBase N = B.kernel.map (QuotientGroup.mk' N) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

instance quotBase_normal : (B.quotBase N).Normal := by
  rw [B.quotBase_eq_map N]
  exact Subgroup.Normal.map B.normal _ (QuotientGroup.mk'_surjective N)

/-- Block-kernel elements as elements of their image. -/
def quotElem : B.kernel →* B.quotBase N := (B.quotChart N).rangeRestrict

theorem quotElem_surjective : Function.Surjective (B.quotElem N) :=
  MonoidHom.rangeRestrict_surjective _

theorem quotElem_eq_one_iff (k : B.kernel) : B.quotElem N k = 1 ↔ (k : G) ∈ N := by
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).mp h'
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr h

theorem quotElem_conj (k : B.kernel) :
    MulAut.conjNormal (QuotientGroup.mk' N B.shift) (B.quotElem N k) =
      B.quotElem N (MulAut.conjNormal B.shift k) := by
  apply Subtype.ext
  simp only [MulAut.conjNormal_apply]
  change QuotientGroup.mk' N B.shift * QuotientGroup.mk' N (k : G) *
      (QuotientGroup.mk' N B.shift)⁻¹ = QuotientGroup.mk' N (B.shift * (k : G) * B.shift⁻¹)
  rw [map_mul, map_mul, map_inv]

theorem quotBase_comm (a b : B.quotBase N) : a * b = b * a := by
  obtain ⟨k, rfl⟩ := B.quotElem_surjective N a
  obtain ⟨k', rfl⟩ := B.quotElem_surjective N b
  rw [← map_mul, ← map_mul, B.kernel_comm]

theorem quotBase_sq (a : B.quotBase N) : a ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := B.quotElem_surjective N a
  rw [← map_pow, B.kernel_sq, map_one]

theorem quotBase_inv (a : B.quotBase N) : a⁻¹ = a := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, B.quotBase_sq]

theorem quotBase_cube [Finite G] (x : G ⧸ N) : x ^ 3 ∈ B.quotBase N := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  exact MonoidHom.mem_range.mpr ⟨⟨g ^ 3, B.cube_mem g⟩, by simp [quotChart]⟩

theorem quotient_card_le [Finite G] :
    Nat.card ((G ⧸ N) ⧸ B.quotBase N) ≤ 3 := by
  have hle : B.kernel ≤ (B.quotBase N).comap (QuotientGroup.mk' N) :=
    fun k hk => MonoidHom.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩
  let m := QuotientGroup.map B.kernel (B.quotBase N) (QuotientGroup.mk' N) hle
  have hm : Function.Surjective m := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact ⟨QuotientGroup.mk g, rfl⟩
  rw [← B.index_three]
  exact Nat.card_le_card_of_surjective m hm

/-- When the shift acts nontrivially on the image, one binary coordinate
functional vanishes on the axis and detects the image with its two shifts. -/
theorem exists_coordinate_label
    (hσ : ∃ v : B.quotBase N, MulAut.conjNormal (QuotientGroup.mk' N B.shift) v ≠ v) :
    ∃ ℓ : (Fin 3 → ZMod 2) →+ ZMod 2,
      (∀ k : B.kernel, (k : G) ∈ N → ℓ (B.chart k).toAdd = 0) ∧
      (∀ k : B.kernel, ℓ (B.chart k).toAdd = 0 →
        ℓ (B.chart (MulAut.conjNormal B.shift k)).toAdd = 0 →
        ℓ (B.chart (MulAut.conjNormal B.shift (MulAut.conjNormal B.shift k))).toAdd = 0 →
        (k : G) ∈ N) := by
  have hone : ∀ k : B.kernel, (B.chart k).toAdd = 0 → k = 1 := by
    intro k hk
    apply B.chart_injective
    rw [map_one, ← ofAdd_toAdd (B.chart k), hk, ofAdd_zero]
  by_cases hS : ∀ k : B.kernel, (k : G) ∈ N → k = 1
  · refine ⟨Pi.evalAddMonoidHom (fun _ : Fin 3 => ZMod 2) 0, fun k hk => ?_,
      fun k h0 h1 h2 => ?_⟩
    · rw [hS k hk, map_one]
      rfl
    · simp only [Pi.evalAddMonoidHom_apply, B.chart_conj] at h0 h1 h2
      rw [hone k (rotThree_detect _ h0 h1 h2)]
      exact N.one_mem
  · push Not at hS
    obtain ⟨k0, hk0N, hk0⟩ := hS
    have hdiag : ∀ k : B.kernel, (k : G) ∈ N →
        (B.chart k).toAdd = 0 ∨ (B.chart k).toAdd = fun _ => 1 := by
      intro k hkN
      by_contra hnot
      push Not at hnot
      obtain ⟨v, hv⟩ := hσ
      apply hv
      obtain ⟨u, rfl⟩ := B.quotElem_surjective N v
      rw [B.quotElem_conj]
      obtain ⟨a, b, c, habc⟩ :=
        rotThree_generate (B.chart k).toAdd (B.chart u).toAdd hnot.1 hnot.2
      have heq : MulAut.conjNormal B.shift u * u =
          k ^ a.val * (MulAut.conjNormal B.shift k) ^ b.val *
            (MulAut.conjNormal B.shift (MulAut.conjNormal B.shift k)) ^ c.val := by
        apply B.chart_injective
        apply Multiplicative.toAdd.injective
        funext i
        simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, Pi.add_apply, Pi.smul_apply,
          B.chart_conj]
        simp only [nsmul_eq_mul, ZMod.natCast_zmod_val]
        exact habc i
      have hk1 : ((MulAut.conjNormal B.shift k : B.kernel) : G) ∈ N := by
        rw [MulAut.conjNormal_apply]
        exact ‹N.Normal›.conj_mem _ hkN _
      have hk2 : ((MulAut.conjNormal B.shift (MulAut.conjNormal B.shift k) : B.kernel) : G) ∈
          N := by
        rw [MulAut.conjNormal_apply]
        exact ‹N.Normal›.conj_mem _ hk1 _
      have hmem : ((MulAut.conjNormal B.shift u * u : B.kernel) : G) ∈ N := by
        rw [heq]
        simp only [Subgroup.coe_mul, Subgroup.coe_pow]
        exact N.mul_mem (N.mul_mem (N.pow_mem hkN _) (N.pow_mem hk1 _)) (N.pow_mem hk2 _)
      have h1 := (B.quotElem_eq_one_iff N _).mpr hmem
      rw [map_mul] at h1
      rw [← B.quotBase_inv N (B.quotElem N u)]
      exact eq_inv_of_mul_eq_one_left h1
    have hk0diag : (B.chart k0).toAdd = fun _ => 1 := by
      rcases hdiag k0 hk0N with h | h
      · exact absurd (hone k0 h) hk0
      · exact h
    refine ⟨Pi.evalAddMonoidHom (fun _ : Fin 3 => ZMod 2) 0 +
        Pi.evalAddMonoidHom (fun _ : Fin 3 => ZMod 2) (rotThree 0), fun k hk => ?_,
      fun k h0 h1 h2 => ?_⟩
    · simp only [AddMonoidHom.add_apply, Pi.evalAddMonoidHom_apply]
      rcases hdiag k hk with h | h
      · rw [h]
        simp
      · rw [h]
        exact zmodTwo_one_add_one
    · simp only [AddMonoidHom.add_apply, Pi.evalAddMonoidHom_apply, B.chart_conj] at h0 h1 h2
      rcases rotThree_pair_detect _ h0 h1 h2 with h | h
      · rw [hone k h]
        exact N.one_mem
      · have hkk0 : k = k0 := B.chart_injective (by
          rw [← ofAdd_toAdd (B.chart k), ← ofAdd_toAdd (B.chart k0), h, hk0diag])
        rw [hkk0]
        exact hk0N

/-- The coordinate functional descends to a triple-detecting label on the
image of the block kernel. -/
theorem exists_quotient_label
    (hσ : ∃ v : B.quotBase N, MulAut.conjNormal (QuotientGroup.mk' N B.shift) v ≠ v) :
    ∃ ι : B.quotBase N →* Multiplicative (ZMod 2), ∀ v : B.quotBase N, ι v = 1 →
      ι (MulAut.conjNormal (QuotientGroup.mk' N B.shift) v) = 1 →
      ι (MulAut.conjNormal (QuotientGroup.mk' N B.shift)
        (MulAut.conjNormal (QuotientGroup.mk' N B.shift) v)) = 1 → v = 1 := by
  obtain ⟨ℓ, hℓN, hℓ⟩ := B.exists_coordinate_label N hσ
  let ιK : B.kernel →* Multiplicative (ZMod 2) :=
    (AddMonoidHom.toMultiplicative ℓ).comp B.chart
  have hιK : ∀ k, ιK k = 1 ↔ ℓ (B.chart k).toAdd = 0 := by
    intro k
    show Multiplicative.ofAdd (ℓ (B.chart k).toAdd) = 1 ↔ _
    exact ofAdd_eq_one
  obtain ⟨ι, hι⟩ := exists_rangeLift_of_ker (B.quotChart N) ιK
    (fun k hk => (hιK k).mpr (hℓN k ((QuotientGroup.eq_one_iff _).mp hk)))
  have hι' : ∀ k, ι (B.quotElem N k) = ιK k := hι
  refine ⟨ι, fun v h0 h1 h2 => ?_⟩
  obtain ⟨k, rfl⟩ := B.quotElem_surjective N v
  simp only [B.quotElem_conj, hι', hιK] at h0 h1 h2
  exact (B.quotElem_eq_one_iff N k).mpr (hℓ k h0 h1 h2)

/-- The nontrivial-shift quotients are bounded by the binary characters of
the source. -/
theorem frobenius_bound [Finite G]
    (hσ : ∃ v : B.quotBase N, MulAut.conjNormal (QuotientGroup.mk' N B.shift) v ≠ v)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ N)) : ℝ) ≤
      Nat.card ((G ⧸ N) ≃* (G ⧸ N)) * (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
  letI : Fintype ((G ⧸ N) ⧸ B.quotBase N) := Fintype.ofFinite _
  have hA := B.quotBase_comm N
  have hc : QuotientGroup.mk' N B.shift ∉ B.quotBase N := by
    intro hcA
    obtain ⟨v, hv⟩ := hσ
    exact hv (conjNormal_self_of_mem (B.quotBase N) hA hcA v)
  have hindex : Nat.card ((G ⧸ N) ⧸ B.quotBase N) = 3 := by
    have hle := B.quotient_card_le N
    have hne : (QuotientGroup.mk (QuotientGroup.mk' N B.shift) :
        (G ⧸ N) ⧸ B.quotBase N) ≠ 1 :=
      fun h => hc ((QuotientGroup.eq_one_iff _).mp h)
    have h3 : (QuotientGroup.mk (QuotientGroup.mk' N B.shift) :
        (G ⧸ N) ⧸ B.quotBase N) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact B.quotBase_cube N _
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hord := orderOf_eq_prime h3 hne
    have hdvd := orderOf_dvd_natCard
      (QuotientGroup.mk (QuotientGroup.mk' N B.shift) : (G ⧸ N) ⧸ B.quotBase N)
    rw [hord] at hdvd
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega
  obtain ⟨ι, hι⟩ := B.exists_quotient_label N hσ
  have hlab := groupEpimorphism_card_le_binaryFrobenius (J := J) (B.quotBase N) hA
    (B.quotBase_sq N) (B.quotBase_cube N) _ hc hindex ι hι hσ
  exact binaryLabel_real_bound b J hlab

/-- With trivial shift action, the coordinate sum shows that the image of
the block kernel has order at most two. -/
theorem quotBase_card_le_two
    (htriv : ∀ v : B.quotBase N, MulAut.conjNormal (QuotientGroup.mk' N B.shift) v = v) :
    Nat.card (B.quotBase N) ≤ 2 := by
  let s : B.kernel → ZMod 2 := fun k =>
    (B.chart k).toAdd 0 + (B.chart k).toAdd 1 + (B.chart k).toAdd 2
  have hsdef : ∀ k, s k = (B.chart k).toAdd 0 + (B.chart k).toAdd 1 + (B.chart k).toAdd 2 :=
    fun k => rfl
  have hs_mul : ∀ k k', s (k * k') = s k + s k' := by
    intro k k'
    simp only [hsdef, map_mul, toAdd_mul, Pi.add_apply]
    ring
  have hfix : ∀ k, B.quotElem N (MulAut.conjNormal B.shift k) = B.quotElem N k := by
    intro k
    rw [← B.quotElem_conj]
    exact htriv _
  have hzero : ∀ k, s k = 0 → B.quotElem N k = 1 := by
    intro k hk
    have hsplit : MulAut.conjNormal B.shift k *
        MulAut.conjNormal B.shift (MulAut.conjNormal B.shift k) = k := by
      apply B.chart_injective
      apply Multiplicative.toAdd.injective
      funext i
      simp only [map_mul, toAdd_mul, Pi.add_apply, B.chart_conj]
      rw [rotThree_trace, ← hsdef, hk, add_zero]
    have h := congrArg (B.quotElem N) hsplit
    simp only [map_mul, hfix] at h
    have h' := congrArg (fun x => (B.quotElem N k)⁻¹ * x) h
    simpa using h'
  have huniq : ∀ a a' : B.quotBase N, a ≠ 1 → a' ≠ 1 → a = a' := by
    intro a a' ha ha'
    obtain ⟨k, rfl⟩ := B.quotElem_surjective N a
    obtain ⟨k', rfl⟩ := B.quotElem_surjective N a'
    have hk : s k = 1 := zmodTwo_eq_one_of_ne_zero _ (fun h => ha (hzero k h))
    have hk' : s k' = 1 := zmodTwo_eq_one_of_ne_zero _ (fun h => ha' (hzero k' h))
    have hprod : B.quotElem N (k * k') = 1 :=
      hzero _ (by rw [hs_mul, hk, hk']; exact zmodTwo_one_add_one)
    rw [map_mul] at hprod
    rw [← B.quotBase_inv N (B.quotElem N k')]
    exact eq_inv_of_mul_eq_one_left hprod
  let f : B.quotBase N → Bool := fun a => decide (a = 1)
  have hf : Function.Injective f := by
    intro a a' h
    by_cases ha : a = 1 <;> by_cases ha' : a' = 1
    · rw [ha, ha']
    · simp [f, ha, ha'] at h
    · simp [f, ha, ha'] at h
    · exact huniq a a' ha ha'
  calc Nat.card (B.quotBase N) ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
    _ = 2 := by simp

/-- The trivial-shift quotients are abelian with a sixfold embedding. -/
theorem abelian_bound [Finite G] (hKP : KovacsPraegerAbelianizationBound)
    (htriv : ∀ v : B.quotBase N, MulAut.conjNormal (QuotientGroup.mk' N B.shift) v = v)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ N)) : ℝ) ≤ (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcA : ∀ a ∈ B.quotBase N, Commute (QuotientGroup.mk' N B.shift) a := by
    intro a ha
    have h := congrArg Subtype.val (htriv ⟨a, ha⟩)
    simp only [MulAut.conjNormal_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hAA : ∀ a ∈ B.quotBase N, ∀ a' ∈ B.quotBase N, Commute a a' :=
    fun a ha a' ha' => congrArg Subtype.val (B.quotBase_comm N ⟨a, ha⟩ ⟨a', ha'⟩)
  have hform : ∀ x : G ⧸ N, ∃ z : ℤ, ∃ a ∈ B.quotBase N,
      x = QuotientGroup.mk' N B.shift ^ z * a := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨z, k, hk, rfl⟩ := B.exists_zpow_mul g
    exact ⟨z, QuotientGroup.mk' N k, MonoidHom.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩,
      by rw [map_mul, map_zpow]⟩
  have hQcomm : ∀ x y : G ⧸ N, Commute x y := by
    intro x y
    obtain ⟨z, a, ha, rfl⟩ := hform x
    obtain ⟨w, a', ha', rfl⟩ := hform y
    exact ((Commute.zpow_zpow_self _ z w).mul_right ((hcA a' ha').zpow_left z)).mul_left
      (((hcA a ha).zpow_left w).symm.mul_right (hAA a ha a' ha'))
  letI : Fintype ((G ⧸ N) ⧸ B.quotBase N) := Fintype.ofFinite _
  have hQA3 : IsPGroup 3 ((G ⧸ N) ⧸ B.quotBase N) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact B.quotBase_cube N x
  obtain ⟨e3, he3⟩ := exists_injective_zmod_of_card_le 3 hQA3 (B.quotient_card_le N)
  have hA2 : IsPGroup 2 (B.quotBase N) := fun a => ⟨1, by rw [pow_one]; exact B.quotBase_sq N a⟩
  obtain ⟨e2, he2⟩ := exists_injective_zmod_of_card_le 2 hA2 (B.quotBase_card_le_two N htriv)
  let cube : (G ⧸ N) →* B.quotBase N :=
    { toFun := fun x => ⟨x ^ 3, B.quotBase_cube N x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        exact (hQcomm x y).mul_pow 3 }
  let ι₂ : (G ⧸ N) →* Multiplicative (ZMod 2) := e2.comp cube
  let ι₃ : (G ⧸ N) →* Multiplicative (ZMod 3) := e3.comp (QuotientGroup.mk' (B.quotBase N))
  have hjoint : ∀ x : G ⧸ N, ι₂ x = 1 → ι₃ x = 1 → x = 1 := by
    intro x h2 h3
    have hcube : x ^ 3 = 1 := congrArg Subtype.val (he2 (h2.trans e2.map_one.symm))
    have hxA : x ∈ B.quotBase N :=
      (QuotientGroup.eq_one_iff x).mp (he3 (h3.trans e3.map_one.symm))
    have hsq : x ^ 2 = 1 := congrArg Subtype.val (B.quotBase_sq N ⟨x, hxA⟩)
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hcube, hsq, inv_one, one_mul]
  exact (groupEpimorphism_card_le_of_kovacsPraeger hKP ι₂ ι₃ hjoint b J).trans
    (kovacsPraeger_real_bound b)

include B in
/-- The uniform quotient-epimorphism bound for one original normal axis. -/
theorem quotientEpimorphism_bound [Finite G] (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ N)) : ℝ) ≤
      ((Nat.card ((G ⧸ N) ≃* (G ⧸ N)) : ℝ) + 1) * (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
  have hE : (0 : ℝ) ≤ (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by positivity
  have haut : (0 : ℝ) ≤ Nat.card ((G ⧸ N) ≃* (G ⧸ N)) := Nat.cast_nonneg _
  by_cases hσ : ∃ v : B.quotBase N, MulAut.conjNormal (QuotientGroup.mk' N B.shift) v ≠ v
  · calc _ ≤ _ := B.frobenius_bound N hσ b J
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE
  · push Not at hσ
    calc _ ≤ _ := B.abelian_bound N hKP hσ b J
      _ ≤ _ := le_mul_of_one_le_left hE (by linarith)

end Quotient

end BinaryBlockCoordinates

/-- A binary pair frame on three blocks whose actual top has order three
supplies the literal block coordinates. -/
theorem BinaryPairFrame.blockCoordinates_nonempty {Ω : Type*}
    {U : Subgroup (Equiv.Perm Ω)} (F : BinaryPairFrame U (Fin 3))
    (hTop : Nat.card F.top.range = 3) : Nonempty (BinaryBlockCoordinates U) := by
  haveI : Finite F.top.range := Nat.finite_of_card_ne_zero (by rw [hTop]; norm_num)
  obtain ⟨g, hg⟩ : ∃ g : F.top.range, g ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : Nat.card F.top.range = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    omega
  have hg3 : (g : Equiv.Perm (Fin 3)) ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := g)
    rw [hTop] at h
    exact congrArg Subtype.val h
  have hg1 : (g : Equiv.Perm (Fin 3)) ≠ 1 := fun h => hg (Subtype.ext h)
  have hmem : rotThree⁻¹ ∈ F.top.range := by
    rcases rotThree_inv_of_order_three _ hg1 hg3 with h | h
    · rw [← h]
      exact g.2
    · rw [← h]
      exact F.top.range.pow_mem g.2 2
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
  exact ⟨{
    kernel := F.top.ker
    normal := inferInstance
    index_three := by
      show F.top.ker.index = 3
      rw [Subgroup.index_ker]
      exact hTop
    chart := F.bitsHom
    chart_injective := F.bitsHom_injective
    shift := u
    shift_not_mem := fun h => rotThree_inv_ne_one (hu.symm.trans (MonoidHom.mem_ker.mp h))
    chart_conj := fun k i => by
      change F.bits (MulAut.conjNormal u k) i = F.bits k (rotThree i)
      rw [F.bits_conjNormal, hu, inv_inv] }⟩

end SymmetricSubgroupAsymptotics

end
