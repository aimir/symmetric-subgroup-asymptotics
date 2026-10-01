import SymmetricSubgroupAsymptotics.Non2PreE7DerivedHead
import SymmetricSubgroupAsymptotics.Non2PreE7HeadFamilyCount
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters

/-!
# The common-head onto count

Let `V = Q^(n+1)` be an elementary abelian `p`-group which is minimal normal,
self-centralizing, and absorbed below `Q^(n)`.  For an arbitrary source `J`
put `F = J^(n+1)`.  Every onto map `φ : J → Q` restricts onto `V` on this ONE
common `F`; pulling back the characters of `V` gives an irreducible invariant
subspace `Λ_φ` of the character space of `F`, of dimension `m = dim V`.  The
subspace `Λ_φ` determines `ker φ ∩ F`, hence `ker φ`.

All these subspaces lie in the same character space of `F`.  The common-head
family count therefore gives

`|Epi(J, Q)| ≤ |Aut Q| · (1 + q + ⋯ + q^k)`,  `k = ⌊d_p(F) / m⌋`,

where `q` bounds the vectors fixed by the stabilizer of one nonzero character
of `V`.  For natural `S₄` this is `m = 2`, `q = 2`, `F = J''`, and the
exponent is `b/4`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DerivedHead

variable (p : ℕ) [Fact p.Prime]

/-- Conjugation on the characters of a normal subgroup. -/
def conjRep (G : Type*) [Group G] (H : Subgroup G) [H.Normal] :
    Representation (ZMod p) G (PrimeCharacters p H) where
  toFun g :=
    { toFun := fun χ => χ.comp (MulAut.conjNormal g⁻¹).toMonoidHom.toAdditive
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext χ h
    show χ (Additive.ofMul (MulAut.conjNormal (1 : G)⁻¹ (Additive.toMul h))) = χ h
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    simp
  map_mul' g g' := by
    ext χ h
    show χ (Additive.ofMul (MulAut.conjNormal (g * g')⁻¹ (Additive.toMul h))) =
      χ (Additive.ofMul (MulAut.conjNormal g'⁻¹
        (MulAut.conjNormal g⁻¹ (Additive.toMul h))))
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [mul_assoc]

theorem conjRep_apply (G : Type*) [Group G] (H : Subgroup G) [H.Normal] (g : G)
    (χ : PrimeCharacters p H) (h : H) :
    conjRep p G H g χ (Additive.ofMul h) =
      χ (Additive.ofMul (MulAut.conjNormal g⁻¹ h)) := rfl

variable {Q : Type} [Group Q]

/-! ## Characters of an elementary abelian normal subgroup -/

/-- Characters separate the points of an additive group of exponent `p`. -/
theorem additive_characters_separate (A : Type) [AddCommGroup A] (h : ∀ x : A, p • x = 0)
    (a : A) (hz : ∀ χ : A →+ ZMod p, χ a = 0) : a = 0 := by
  letI : Module (ZMod p) A := AddCommGroup.zmodModule (n := p) h
  exact (Module.forall_dual_apply_eq_zero_iff (ZMod p) a).mp (fun φ => hz φ.toAddMonoidHom)

/-- Characters separate the points of an elementary abelian group. -/
theorem characters_separate (V : Subgroup Q)
    (hcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hexp : ∀ v ∈ V, v ^ p = 1)
    (v : V) (h : ∀ χ : PrimeCharacters p V, χ (Additive.ofMul v) = 0) : v = 1 := by
  letI : AddCommGroup (Additive V) :=
    { (inferInstance : AddGroup (Additive V)) with
      add_comm := fun a b => by
        change Additive.ofMul (Additive.toMul a * Additive.toMul b) =
          Additive.ofMul (Additive.toMul b * Additive.toMul a)
        congr 1
        exact Subtype.ext (hcomm _ (Additive.toMul a).2 _ (Additive.toMul b).2) }
  have h0 := additive_characters_separate p (Additive V) (fun x => by
      change Additive.ofMul ((Additive.toMul x) ^ p) = Additive.ofMul 1
      congr 1
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hexp _ (Additive.toMul x).2)
    (Additive.ofMul v) (fun χ => h χ)
  exact Additive.ofMul.injective h0

/-- An invariant subspace of the characters of a minimal normal elementary
abelian subgroup is zero or everything. -/
theorem characters_invariant_dichotomy [Finite Q] (V : Subgroup Q) [hVn : V.Normal]
    (hmin : ∀ W : Subgroup Q, W.Normal → W ≤ V → W = ⊥ ∨ W = V)
    (S : Submodule (ZMod p) (PrimeCharacters p V))
    (hS : Invariant (conjRep p Q V) S) : S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  -- the common kernel of `S` is a normal subgroup below `V`
  let A : Subgroup Q :=
    { carrier := {x | ∃ hx : x ∈ V, ∀ χ ∈ S, χ (Additive.ofMul (⟨x, hx⟩ : V)) = 0}
      one_mem' := ⟨V.one_mem, fun χ _ => χ.map_zero⟩
      mul_mem' := by
        rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
        refine ⟨V.mul_mem ha hb, fun χ hχ => ?_⟩
        have : (Additive.ofMul (⟨a * b, V.mul_mem ha hb⟩ : V)) =
            Additive.ofMul (⟨a, ha⟩ : V) + Additive.ofMul (⟨b, hb⟩ : V) := rfl
        rw [this, map_add, hA χ hχ, hB χ hχ, add_zero]
      inv_mem' := by
        rintro a ⟨ha, hA⟩
        refine ⟨V.inv_mem ha, fun χ hχ => ?_⟩
        have : (Additive.ofMul (⟨a⁻¹, V.inv_mem ha⟩ : V)) =
            -Additive.ofMul (⟨a, ha⟩ : V) := rfl
        rw [this, map_neg, hA χ hχ, neg_zero] }
  have hAn : A.Normal := by
    constructor
    rintro x ⟨hx, hX⟩ g
    refine ⟨hVn.conj_mem x hx g, fun χ hχ => ?_⟩
    have hχ' := hS g⁻¹ χ hχ
    have := hX _ hχ'
    rw [conjRep_apply] at this
    convert this using 3
    apply Subtype.ext
    simp
  have hAV : A ≤ V := fun x hx => hx.1
  have hAbot : A = ⊥ := by
    rcases hmin A hAn hAV with h | h
    · exact h
    · exfalso
      apply hbot
      rw [eq_bot_iff]
      intro χ hχ
      rw [Submodule.mem_bot]
      ext w
      have hw : (w : Q) ∈ A := by
        rw [h]
        exact w.2
      obtain ⟨_, hW⟩ := hw
      exact hW χ hχ
  by_contra htop
  obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
    by_contra hall
    push Not at hall
    exact htop (eq_top_iff.mpr fun x _ => hall x)
  obtain ⟨Φ, hΦx, hΦS⟩ := S.exists_dual_map_eq_bot_of_notMem hx inferInstance
  obtain ⟨v, hv⟩ := primeAbelianizationMap_surjective p V Φ
  have hvA : ((Additive.toMul v : V) : Q) ∈ A := by
    refine ⟨(Additive.toMul v).2, fun χ hχ => ?_⟩
    have : Φ χ = 0 := by
      have hmem : Φ χ ∈ S.map Φ := ⟨χ, hχ, rfl⟩
      rw [hΦS] at hmem
      exact (Submodule.mem_bot _).mp hmem
    rw [← hv] at this
    exact this
  rw [hAbot] at hvA
  have hv1 : v = 0 := by
    apply Additive.toMul.injective
    exact Subtype.ext ((Subgroup.mem_bot).mp hvA)
  apply hΦx
  rw [← hv, hv1, map_zero]
  rfl

/-! ## The pulled-back subspaces -/

variable {J : Type} [Group J]

/-- Pull back the characters of `V` along the restriction to `F`. -/
def pullback (F : Subgroup J) (V : Subgroup Q) (φ : J →* Q) (hφ : F.map φ = V) :
    PrimeCharacters p V →ₗ[ZMod p] PrimeCharacters p F :=
  primeCharacterInflation p (restriction F V φ hφ)

theorem pullback_injective (F : Subgroup J) (V : Subgroup Q) (φ : J →* Q)
    (hφ : F.map φ = V) : Function.Injective (pullback p F V φ hφ) := by
  apply primeCharacterInflation_injective
  rintro ⟨v, hv⟩
  rw [← hφ] at hv
  obtain ⟨f, hf, rfl⟩ := hv
  exact ⟨⟨f, hf⟩, rfl⟩

theorem pullback_intertwine (F : Subgroup J) [F.Normal] (V : Subgroup Q) [V.Normal]
    (φ : J →* Q) (hφ : F.map φ = V) (g : J) (χ : PrimeCharacters p V) :
    conjRep p J F g (pullback p F V φ hφ χ) =
      pullback p F V φ hφ (conjRep p Q V (φ g) χ) := by
  ext f
  show χ (Additive.ofMul (restriction F V φ hφ (MulAut.conjNormal g⁻¹ (Additive.toMul f)))) =
    χ (Additive.ofMul (MulAut.conjNormal (φ g)⁻¹ (restriction F V φ hφ (Additive.toMul f))))
  congr 2
  apply Subtype.ext
  simp [restriction_apply]

/-- The pulled-back subspace of one onto map. -/
def headSpace (F : Subgroup J) (V : Subgroup Q) (φ : J →* Q) (hφ : F.map φ = V) :
    Submodule (ZMod p) (PrimeCharacters p F) :=
  LinearMap.range (pullback p F V φ hφ)

/-- The head space determines the kernel on `F`. -/
theorem mem_ker_iff_headSpace (F : Subgroup J) (V : Subgroup Q)
    (hcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hexp : ∀ v ∈ V, v ^ p = 1)
    (φ : J →* Q) (hφ : F.map φ = V) (f : F) :
    φ f = 1 ↔ ∀ ℓ ∈ headSpace p F V φ hφ, ℓ (Additive.ofMul f) = 0 := by
  constructor
  · rintro hf _ ⟨χ, rfl⟩
    have : restriction F V φ hφ f = 1 := Subtype.ext (by simp [restriction_apply, hf])
    show χ (Additive.ofMul (restriction F V φ hφ f)) = 0
    rw [this]
    exact χ.map_zero
  · intro h
    have := characters_separate p V hcomm hexp (restriction F V φ hφ f)
      (fun χ => h _ ⟨χ, rfl⟩)
    exact congrArg Subtype.val this

/-! ## The target structure and the count -/

instance derivedSeries_normal' (G : Type*) [Group G] (k : ℕ) : (derivedSeries G k).Normal :=
  derivedSeries_normal G k

/-- A target whose `(n+1)`-st derived term is an elementary abelian minimal
normal, self-centralizing, absorbed subgroup of dimension `m`, with one
nonzero character whose stabilizer fixes at most `q` characters. -/
structure DerivedHeadTarget (Q : Type*) [Group Q] (n m q : ℕ) : Prop where
  self_centralizing : ∀ x : Q, (∀ v ∈ derivedSeries Q (n + 1), x * v = v * x) →
    x ∈ derivedSeries Q (n + 1)
  absorbing : ∀ W : Subgroup Q, W.Normal → W ≤ derivedSeries Q (n + 1) →
    W ≤ ⁅derivedSeries Q n, W⁆
  commutative : ∀ v ∈ derivedSeries Q (n + 1), ∀ w ∈ derivedSeries Q (n + 1), v * w = w * v
  exponent : ∀ v ∈ derivedSeries Q (n + 1), v ^ p = 1
  minimal : ∀ W : Subgroup Q, W.Normal → W ≤ derivedSeries Q (n + 1) →
    W = ⊥ ∨ W = derivedSeries Q (n + 1)
  finrank_eq : Module.finrank (ZMod p) (PrimeCharacters p (derivedSeries Q (n + 1))) = m
  witness : ∃ χ₀ : PrimeCharacters p (derivedSeries Q (n + 1)), χ₀ ≠ 0 ∧
    Nat.card {χ : PrimeCharacters p (derivedSeries Q (n + 1)) //
      ∀ x : Q, conjRep p Q _ x χ₀ = χ₀ → conjRep p Q _ x χ = χ} ≤ q

namespace DerivedHeadTarget

variable {p} {n m q : ℕ}

/-- Every onto map gives a member of the common head of `F = J^(n+1)`. -/
theorem headMember [Finite Q] (D : DerivedHeadTarget p Q n m q) (φ : GroupEpimorphism J Q) :
    HeadMember (conjRep p J (derivedSeries J (n + 1))) m q
      (headSpace p (derivedSeries J (n + 1)) (derivedSeries Q (n + 1)) φ.1
        (map_derivedSeries_eq φ.2 (n + 1))) := by
  set F := derivedSeries J (n + 1)
  set V := derivedSeries Q (n + 1)
  have hφ : F.map φ.1 = V := map_derivedSeries_eq φ.2 (n + 1)
  set L := pullback p F V φ.1 hφ
  have hL := pullback_injective p F V φ.1 hφ
  obtain ⟨χ₀, hχ₀, hcard⟩ := D.witness
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro g _ ⟨χ, rfl⟩
    exact ⟨_, (pullback_intertwine p F V φ.1 hφ g χ).symm⟩
  · intro hbot
    apply hχ₀
    apply hL
    have : L χ₀ ∈ headSpace p F V φ.1 hφ := ⟨χ₀, rfl⟩
    rw [hbot] at this
    rw [(Submodule.mem_bot _).mp this, map_zero]
  · intro W' hle hinv
    let S₀ : Submodule (ZMod p) (PrimeCharacters p V) := W'.comap L
    have hS₀ : Invariant (conjRep p Q V) S₀ := by
      intro x χ hχ
      obtain ⟨g, rfl⟩ := φ.2 x
      show L (conjRep p Q V (φ.1 g) χ) ∈ W'
      rw [← pullback_intertwine]
      exact hinv g _ hχ
    have hW' : W' = S₀.map L := by
      rw [Submodule.map_comap_eq]
      exact (inf_eq_right.mpr hle).symm
    rcases characters_invariant_dichotomy p V D.minimal S₀ hS₀
      with h | h
    · left
      rw [hW', h, Submodule.map_bot]
    · right
      rw [hW', h, Submodule.map_top]
      rfl
  · rw [headSpace, LinearMap.finrank_range_of_inj hL, D.finrank_eq]
  · refine ⟨L χ₀, ⟨χ₀, rfl⟩, fun h0 => hχ₀ (hL (by rw [h0, map_zero])), ?_⟩
    let back : {x : headSpace p F V φ.1 hφ //
        ∀ g : J, conjRep p J F g (L χ₀) = L χ₀ → conjRep p J F g (x : PrimeCharacters p F) = x} →
        {χ : PrimeCharacters p V //
          ∀ x : Q, conjRep p Q V x χ₀ = χ₀ → conjRep p Q V x χ = χ} := fun x =>
      Subtype.mk (Classical.choose x.1.2) (fun y hy => by
        obtain ⟨g, rfl⟩ := φ.2 y
        have hspec : L (Classical.choose x.1.2) = x.1 := Classical.choose_spec x.1.2
        apply hL
        rw [← pullback_intertwine, hspec]
        apply x.2 g
        rw [pullback_intertwine, hy])
    have hback : Function.Injective back := by
      intro x x' hxx
      have h1 := congrArg Subtype.val hxx
      simp only [back] at h1
      have e1 : L (Classical.choose x.1.2) = x.1 := Classical.choose_spec x.1.2
      have e2 : L (Classical.choose x'.1.2) = x'.1 := Classical.choose_spec x'.1.2
      apply Subtype.ext
      apply Subtype.ext
      rw [← e1, ← e2, h1]
    exact (Nat.card_le_card_of_injective back hback).trans hcard

/-- **The common-head onto count.** -/
theorem epi_card_le [Finite J] [Finite Q] (D : DerivedHeadTarget p Q n m q) :
    Nat.card (GroupEpimorphism J Q) ≤
      (∑ j ∈ Finset.range
          (Module.finrank (ZMod p) (PrimeCharacters p (derivedSeries J (n + 1))) / m + 1),
        q ^ j) * Nat.card (Q ≃* Q) := by
  set F := derivedSeries J (n + 1)
  set V := derivedSeries Q (n + 1)
  letI : Finite (J →* Q) :=
    Finite.of_injective (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
  letI : Fintype (GroupEpimorphism J Q) := Fintype.ofFinite _
  let label : GroupEpimorphism J Q → Submodule (ZMod p) (PrimeCharacters p F) :=
    fun φ => headSpace p F V φ.1 (map_derivedSeries_eq φ.2 (n + 1))
  let X : Finset (Submodule (ZMod p) (PrimeCharacters p F)) := Finset.univ.image label
  let label' : GroupEpimorphism J Q → X := fun φ =>
    ⟨label φ, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hker : ∀ φ ψ : GroupEpimorphism J Q, label' φ = label' ψ → φ.1.ker = ψ.1.ker := by
    intro φ ψ hl
    have hl' : label φ = label ψ := congrArg Subtype.val hl
    apply ker_eq_of_inf_eq F V φ.1 ψ.1 (map_derivedSeries_eq φ.2 (n + 1))
      (map_derivedSeries_eq ψ.2 (n + 1)) D.self_centralizing
      (fun K hK hKV => derived_lift n D.absorbing φ.1 φ.2 K hK hKV)
      (fun K hK hKV => derived_lift n D.absorbing ψ.1 ψ.2 K hK hKV)
    ext x
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · rintro ⟨hx, hxF⟩
      refine ⟨?_, hxF⟩
      have h1 := (mem_ker_iff_headSpace p F V D.commutative D.exponent φ.1
        (map_derivedSeries_eq φ.2 (n + 1)) ⟨x, hxF⟩).mp hx
      change ∀ ℓ ∈ label φ, _ at h1
      rw [hl'] at h1
      exact (mem_ker_iff_headSpace p F V D.commutative D.exponent ψ.1
        (map_derivedSeries_eq ψ.2 (n + 1)) ⟨x, hxF⟩).mpr h1
    · rintro ⟨hx, hxF⟩
      refine ⟨?_, hxF⟩
      have h1 := (mem_ker_iff_headSpace p F V D.commutative D.exponent ψ.1
        (map_derivedSeries_eq ψ.2 (n + 1)) ⟨x, hxF⟩).mp hx
      change ∀ ℓ ∈ label ψ, _ at h1
      rw [← hl'] at h1
      exact (mem_ker_iff_headSpace p F V D.commutative D.exponent φ.1
        (map_derivedSeries_eq φ.2 (n + 1)) ⟨x, hxF⟩).mpr h1
  have h1 := groupEpimorphism_card_le_kernel_labels label' hker
  have hX : X.card ≤ ∑ j ∈ Finset.range
      (Module.finrank (ZMod p) (PrimeCharacters p F) / m + 1), q ^ j := by
    have hm : 0 < m := by
      obtain ⟨χ₀, hχ₀, _⟩ := D.witness
      rw [← D.finrank_eq]
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      exact ⟨χ₀, hχ₀⟩
    apply card_family_le m q _ (PrimeCharacters p F) (conjRep p J F) X
    · intro W hW
      obtain ⟨φ, _, rfl⟩ := Finset.mem_image.mp hW
      exact D.headMember φ
    · exact Nat.lt_div_mul_add hm |>.trans_le (by ring_nf; omega)
  calc Nat.card (GroupEpimorphism J Q) ≤ Nat.card X * Nat.card (Q ≃* Q) := h1
    _ = X.card * Nat.card (Q ≃* Q) := by rw [Nat.card_eq_finsetCard]
    _ ≤ _ := Nat.mul_le_mul_right _ hX

end DerivedHeadTarget

/-- The geometric sum is at most twice its top term when `q ≥ 2`. -/
theorem geom_sum_le_two_mul (q k : ℕ) (hq : 2 ≤ q) :
    ∑ j ∈ Finset.range (k + 1), q ^ j ≤ 2 * q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have : q ^ (k + 1) = q * q ^ k := by ring
    rw [this]
    nlinarith [Nat.one_le_pow k q (by omega)]

end DerivedHead
end SymmetricSubgroupAsymptotics
