import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelRelabel

/-!
# Comparators through a common factor, central lifts and binary twists

Three reusable pieces for the small fixed-degree owners.

* **Factor comparators.**  The actual group `G` and the comparator `R` map
  onto one common factor `P`.  If every nontrivial normal subgroup of `G`
  contains `ker(G → P)`, every nontrivial literal quotient of `G` is a
  literal quotient of `R`.  The trivial kernel carries a mixed bound.
* **Central lifts.**  Onto maps to a central extension `Q → P` are counted
  by onto maps to `P` times homomorphisms to the central kernel.
* **Binary twists.**  If `A` has no binary character, every pair of an onto
  map to `A` and a binary character of the source is an onto map to
  `A × C₂` or, for the trivial character, to `A`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-! ## Central lifts -/

/-- Onto maps to a central extension: `|Epi(J,Q)| ≤ |Epi(J,P)| · |Hom(J, ker)|`. -/
theorem epi_card_le_centralLift {J Q P : Type*} [Group J] [Group Q] [Group P]
    [Finite J] [Finite Q] [Finite P] (π : Q →* P) (hπ : Function.Surjective π)
    (hcent : ∀ z ∈ π.ker, ∀ q : Q, z * q = q * z) :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (GroupEpimorphism J P) * Nat.card (J →* π.ker) := by
  letI : Finite (J →* Q) := Finite.of_injective (fun f : J →* Q => (f : J → Q))
    DFunLike.coe_injective
  letI : Finite (J →* P) := Finite.of_injective (fun f : J →* P => (f : J → P))
    DFunLike.coe_injective
  letI : Finite (J →* π.ker) := Finite.of_injective (fun f : J →* π.ker => (f : J → π.ker))
    DFunLike.coe_injective
  rcases isEmpty_or_nonempty (GroupEpimorphism J Q) with h | h
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  let F : GroupEpimorphism J Q → GroupEpimorphism J P := fun φ => ⟨π.comp φ.1, hπ.comp φ.2⟩
  let base : GroupEpimorphism J P → GroupEpimorphism J Q := Function.invFun F
  have hbase : ∀ φ, F (base (F φ)) = F φ := fun φ => Function.invFun_eq ⟨φ, rfl⟩
  have hker : ∀ φ x, φ.1 x * ((base (F φ)).1 x)⁻¹ ∈ π.ker := by
    intro φ x
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have := congrArg (fun θ : GroupEpimorphism J P => θ.1 x) (hbase φ)
    simp only [F, MonoidHom.comp_apply] at this
    rw [this, mul_inv_cancel]
  let d : GroupEpimorphism J Q → (J →* π.ker) := fun φ =>
    { toFun := fun x => ⟨φ.1 x * ((base (F φ)).1 x)⁻¹, hker φ x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
        have hy := hcent _ (hker φ y) (φ.1 x)
        have hx := hcent _ (hker φ x) (φ.1 y * ((base (F φ)).1 y)⁻¹)
        calc φ.1 x * φ.1 y * (((base (F φ)).1 y)⁻¹ * ((base (F φ)).1 x)⁻¹)
            = (φ.1 x * (φ.1 y * ((base (F φ)).1 y)⁻¹)) * ((base (F φ)).1 x)⁻¹ := by group
          _ = ((φ.1 y * ((base (F φ)).1 y)⁻¹) * φ.1 x) * ((base (F φ)).1 x)⁻¹ := by
              rw [hy]
          _ = (φ.1 y * ((base (F φ)).1 y)⁻¹) * (φ.1 x * ((base (F φ)).1 x)⁻¹) := by group
          _ = (φ.1 x * ((base (F φ)).1 x)⁻¹) * (φ.1 y * ((base (F φ)).1 y)⁻¹) := hx.symm }
  have hinj : Function.Injective (fun φ => (F φ, d φ)) := by
    intro φ ψ hφψ
    have hF : F φ = F ψ := congrArg Prod.fst hφψ
    have hd : d φ = d ψ := congrArg Prod.snd hφψ
    apply Subtype.ext
    ext x
    have := congrArg (fun f : J →* π.ker => (f x : Q)) hd
    simp only [d, MonoidHom.coe_mk, OneHom.coe_mk] at this
    rw [hF] at this
    exact mul_right_cancel this
  calc Nat.card (GroupEpimorphism J Q)
      ≤ Nat.card (GroupEpimorphism J P × (J →* π.ker)) :=
        Nat.card_le_card_of_injective _ hinj
    _ = _ := Nat.card_prod _ _

/-! ## Binary twists -/

/-- A character of the source which is trivial on the kernel of an onto map
factors through the target. -/
theorem character_factors {J A : Type*} [Group J] [Group A] (f : J →* A)
    (hf : Function.Surjective f) (χ : J →* Multiplicative (ZMod 2))
    (h : ∀ k ∈ f.ker, χ k = 1) : ∃ χ' : A →* Multiplicative (ZMod 2), χ'.comp f = χ :=
  ⟨(QuotientGroup.lift f.ker χ h).comp
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom, by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [show (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x) =
        (x : J ⧸ f.ker) from (MulEquiv.symm_apply_eq _).mpr rfl]
    rfl⟩

/-- Pairs of an onto map to `A` and a binary character are onto maps to
`A × C₂` or, when the character is trivial, onto maps to `A`. -/
theorem epi_mul_hom_two_le {J A : Type*} [Group J] [Group A] [Finite J] [Finite A]
    (hA : ∀ χ : A →* Multiplicative (ZMod 2), χ = 1) :
    Nat.card (GroupEpimorphism J A) * Nat.card (J →* Multiplicative (ZMod 2)) ≤
      Nat.card (GroupEpimorphism J (A × Multiplicative (ZMod 2))) +
        Nat.card (GroupEpimorphism J A) := by
  letI : Finite (J →* A × Multiplicative (ZMod 2)) :=
    Finite.of_injective (fun f : J →* A × Multiplicative (ZMod 2) =>
      (f : J → A × Multiplicative (ZMod 2))) DFunLike.coe_injective
  letI : Finite (J →* A) := Finite.of_injective (fun f : J →* A => (f : J → A))
    DFunLike.coe_injective
  letI : Finite (J →* Multiplicative (ZMod 2)) :=
    Finite.of_injective (fun f : J →* Multiplicative (ZMod 2) =>
      (f : J → Multiplicative (ZMod 2))) DFunLike.coe_injective
  have honto : ∀ (f : GroupEpimorphism J A) (χ : J →* Multiplicative (ZMod 2)), χ ≠ 1 →
      Function.Surjective (f.1.prod χ) := by
    intro f χ hχ
    -- some kernel element of `f` has nontrivial character
    have hk : ∃ k ∈ f.1.ker, χ k ≠ 1 := by
      by_contra hall
      push Not at hall
      obtain ⟨χ', hχ'⟩ := character_factors f.1 f.2 χ hall
      apply hχ
      rw [← hχ', hA χ']
      rfl
    obtain ⟨k, hkf, hkχ⟩ := hk
    have hval : ∀ c : Multiplicative (ZMod 2), c ≠ 1 → c = Multiplicative.ofAdd 1 := by decide
    rintro ⟨a, c⟩
    obtain ⟨x, hx⟩ := f.2 a
    by_cases hc : χ x = c
    · exact ⟨x, Prod.ext hx hc⟩
    · refine ⟨x * k, Prod.ext ?_ ?_⟩
      · show f.1 (x * k) = a
        rw [map_mul, (MonoidHom.mem_ker).mp hkf, mul_one, hx]
      · show χ (x * k) = c
        have h1 : χ (x * k) ≠ χ x := by
          rw [map_mul]
          intro h
          apply hkχ
          exact mul_eq_left.mp h
        -- in `C₂` two distinct values exhaust the group
        have hall : ∀ u v w : Multiplicative (ZMod 2), u ≠ v → w ≠ v → u = w := by decide
        exact hall _ _ _ h1 (fun h => hc h.symm)
  let g : GroupEpimorphism J A × (J →* Multiplicative (ZMod 2)) →
      GroupEpimorphism J (A × Multiplicative (ZMod 2)) ⊕ GroupEpimorphism J A :=
    fun p => if hp : p.2 = 1 then Sum.inr p.1 else Sum.inl ⟨p.1.1.prod p.2, honto p.1 p.2 hp⟩
  have hg : Function.Injective g := by
    rintro ⟨f, χ⟩ ⟨f', χ'⟩ he
    by_cases hχ : χ = 1 <;> by_cases hχ' : χ' = 1 <;> simp only [g, hχ, hχ', dite_true,
      dite_false, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at he
    · rw [he, hχ, hχ']
    · have h1 := congrArg Subtype.val he
      apply Prod.ext
      · apply Subtype.ext
        ext x
        exact congrArg Prod.fst (DFunLike.congr_fun h1 x)
      · ext x
        exact congrArg Prod.snd (DFunLike.congr_fun h1 x)
  calc Nat.card (GroupEpimorphism J A) * Nat.card (J →* Multiplicative (ZMod 2))
      = Nat.card (GroupEpimorphism J A × (J →* Multiplicative (ZMod 2))) :=
        (Nat.card_prod _ _).symm
    _ ≤ Nat.card (GroupEpimorphism J (A × Multiplicative (ZMod 2)) ⊕
          GroupEpimorphism J A) := Nat.card_le_card_of_injective g hg
    _ = _ := Nat.card_sum

/-- Two distinct literal normal axes of `R` contribute two summands of its
complete quotient count. -/
theorem two_axes_le_completeQuotientCount {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    {R : Type*} [Group R] [Finite R] (M₁ M₂ : {M : Subgroup R // M.Normal}) (hne : M₁ ≠ M₂)
    {X₁ X₂ : Type*} [Group X₁] [Group X₂]
    (e₁ : X₁ ≃* R ⧸ M₁.1) (e₂ : X₂ ≃* R ⧸ M₂.1) :
    Nat.card (GroupEpimorphism J X₁) + Nat.card (GroupEpimorphism J X₂) ≤
      completeQuotientCount (R := R) J := by
  rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e₁,
    fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e₂]
  unfold completeQuotientCount
  have hpair := Finset.sum_pair (f := fun N : {N : Subgroup R // N.Normal} =>
    Nat.card (GroupEpimorphism J (R ⧸ N.1))) hne
  rw [← hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Nat.zero_le _)

namespace Non2UnipotentPrefixFiniteMenu

/-! ## Factor comparator models -/

/-- An actual action identified with a model group `G` mapping onto a factor
`P`, onto which the comparator `R` also maps.  Every nontrivial normal
subgroup of `G` contains `ker(G → P)`; the trivial kernel carries a mixed
bound. -/
structure PreE7FactorComparatorModel (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  G : Type
  [groupG : Group G]
  [finiteG : Finite G]
  equiv : preE7NonPairAction w i ≃* G
  P : Type
  [groupP : Group P]
  π : G →* P
  π_surjective : Function.Surjective π
  normal_cover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → π.ker ≤ N
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  degree : ℕ
  action : R →* Equiv.Perm (Fin degree)
  action_injective : Function.Injective action
  σ : R →* P
  σ_surjective : Function.Surjective σ
  tailSlope : ℝ
  mainConstant : ℝ
  tailConstant : ℝ
  mainConstant_nonneg : 0 ≤ mainConstant
  tailConstant_nonneg : 0 ≤ tailConstant
  bottom : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (GroupEpimorphism J G) : ℝ) ≤
      mainConstant * completeQuotientWeight (R := R) J + tailConstant * (2 : ℝ) ^ (tailSlope * b)
  comparator_window : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - ((max 2 degree : ℕ) : ℝ)) / 8
  tail_window : tailSlope ≤ preE7CharacterWindow w

attribute [instance] PreE7FactorComparatorModel.groupG PreE7FactorComparatorModel.finiteG
  PreE7FactorComparatorModel.groupP PreE7FactorComparatorModel.groupR
  PreE7FactorComparatorModel.finiteR

namespace PreE7FactorComparatorModel

variable {w : ℕ} {i : PreE7NonPairActionClass w} (M : PreE7FactorComparatorModel w i)

/-- The certificate on one literal normal axis. -/
def axis (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w i) N M.R M.tailSlope := by
  haveI : N.1.Normal := N.2
  by_cases h : N.1 = ⊥
  · refine .bounded M.mainConstant M.tailConstant M.mainConstant_nonneg
      M.tailConstant_nonneg (fun b J _ => ?_)
    have e : (preE7NonPairAction w i ⧸ N.1) ≃* M.G :=
      (QuotientGroup.quotientMulEquivOfEq h).trans
        ((QuotientGroup.quotientBot).trans M.equiv)
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    exact M.bottom b J
  · let N' : Subgroup M.G := N.1.map M.equiv.toMonoidHom
    haveI hN' : N'.Normal := N.2.map _ M.equiv.surjective
    have hN'b : N' ≠ ⊥ := by
      intro hb
      apply h
      rw [eq_bot_iff]
      intro x hx
      have : M.equiv x ∈ N' := ⟨x, hx, rfl⟩
      rw [hb] at this
      have h1 : M.equiv x = 1 := (Subgroup.mem_bot).mp this
      exact (Subgroup.mem_bot).mpr (M.equiv.injective (h1.trans (map_one _).symm))
    let K : Subgroup M.P := N'.map M.π
    haveI hK : K.Normal := hN'.map _ M.π_surjective
    let L : Subgroup M.R := K.comap M.σ
    haveI hL : L.Normal := hK.comap M.σ
    have hσL : M.σ.ker ≤ L := fun x hx => by
      show M.σ x ∈ K
      rw [(MonoidHom.mem_ker).mp hx]
      exact K.one_mem
    have hLmap : L.map M.σ = K := Subgroup.map_comap_eq_self_of_surjective M.σ_surjective K
    haveI : (L.map M.σ).Normal := hL.map _ M.σ_surjective
    exact .comparator ⟨L, hL⟩
      ((QuotientGroup.congr N.1 N' M.equiv rfl).trans
        ((quotientEquivOfKerLe M.π M.π_surjective N' (M.normal_cover N' hN' hN'b)).trans
          ((QuotientGroup.quotientMulEquivOfEq hLmap).symm.trans
            (quotientEquivOfKerLe M.σ M.σ_surjective L hσL).symm)))

/-- The small additive template data. -/
def toData : PreE7SmallAdditiveData w i where
  R := M.R
  degree := M.degree
  action := M.action
  action_injective := M.action_injective
  tailSlope := M.tailSlope
  comparator_window := M.comparator_window
  tail_window := M.tail_window
  axis := M.axis

include M in
/-- The action is accepted by the mixed local catalogue. -/
theorem localFamilyAction (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    preE7NoPairNoC3EarlierLocalFamilyAction family w i :=
  M.toData.localFamilyAction family

end PreE7FactorComparatorModel

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
