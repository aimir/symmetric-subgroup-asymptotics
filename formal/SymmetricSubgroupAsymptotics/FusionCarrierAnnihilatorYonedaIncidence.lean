import SymmetricSubgroupAsymptotics.FusionCarrierSubdirectCapacity
import SymmetricSubgroupAsymptotics.FusionEpimorphismLifts
import SymmetricSubgroupAsymptotics.Non2LiftBound

/-!
# Annihilator-aware Yoneda incidence for reversible carrier cells

A retained cell of an accepted carrier epimorphism `γ : J ↠ Q` has two
components.  The first is the complete quotient map `J ↠ Q ↠ R/M`, through
a top `τ : Q ↠ R/M` fixed by the carrier axis and never by `γ`.  The second
is a retained flag, which is a function of the literal pullback core
`fusionCarrierSubdirectGraph C J γ`.

Over a fixed top map, the remaining Yoneda fibre is counted one abelian
layer at a time.  At a layer `π : Q ↠ B` with kernel module `A`, fixing the
bottom map and the literal restriction value of the lift leaves exactly the
inflated cocycles, of which there are `|Z¹(B,A)| = |B¹(B,A)| |H¹(B,A)|`.  The
possible flags are the literal restriction range, where the transgression
annihilator is encoded; it is never enlarged to all equivariant kernel maps.
Along a tower of abelian layers the flag counts and fibre bounds multiply:
`|Flag| · Z_Yoneda ≤ ∏ |im res_ℓ| |A_ℓ| |H¹(B_ℓ,A_ℓ)|`.  Empty obstruction
fibres contribute zero.  Nonabelian chief factors are not treated here; an
unowned axis must supply such a tower.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

open groupCohomology

/-! ### The fixed top component and its fibre plumbing -/

section Top

variable {J Q R : Type*} [Group J] [Group Q] [Group R]

/-- The complete quotient-map component of a retained cell: the carrier
epimorphism followed by the fixed top `τ : Q ↠ R/M`. -/
def fusionCarrierTopQuotientMap (M : Subgroup R) [M.Normal]
    (τ : Q →* R ⧸ M) (hτ : Function.Surjective τ)
    (γ : GroupEpimorphism J Q) : CompleteQuotientMap J R :=
  ⟨⟨M, inferInstance⟩, ⟨τ.comp γ.1, hτ.comp γ.2⟩⟩

/-- A fibre of the retained cell `(top map, flag)` is the set of states with
one prescribed top map `J → R/M` and one prescribed flag.  A cell with a
different normal axis is empty. -/
theorem fusionCarrierTopCell_fibre_card_le
    {X A : Type*} [Finite X]
    (M : Subgroup R) [M.Normal] (τ : Q →* R ⧸ M) (hτ : Function.Surjective τ)
    (e : X → GroupEpimorphism J Q) (flag : X → A) (Z : ℕ)
    (h : ∀ (t : J →* R ⧸ M) (a : A),
      Nat.card {x : X // τ.comp (e x).1 = t ∧ flag x = a} ≤ Z)
    (y : CompleteQuotientMap J R × A) :
    Nat.card {x : X //
      (fusionCarrierTopQuotientMap M τ hτ (e x), flag x) = y} ≤ Z := by
  obtain ⟨⟨⟨N', hN'⟩, ε⟩, a⟩ := y
  by_cases hN : N' = M
  · subst hN
    refine le_trans (Nat.card_le_card_of_injective
      (fun x => (⟨x.1, ?_, ?_⟩ : {x : X // τ.comp (e x).1 = ε.1 ∧ flag x = a}))
      ?_) (h ε.1 a)
    · have h1 := (Prod.mk.inj x.2).1
      have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h1).2
      exact congrArg Subtype.val h2
    · exact (Prod.mk.inj x.2).2
    · intro x y hxy
      have hxy' := congrArg Subtype.val hxy
      exact Subtype.ext hxy'
  · haveI : IsEmpty {x : X //
        (fusionCarrierTopQuotientMap M τ hτ (e x), flag x) =
          (⟨⟨N', hN'⟩, ε⟩, a)} := by
      refine ⟨fun x => hN ?_⟩
      have h1 := (Prod.mk.inj x.2).1
      have h2 := (Sigma.mk.inj_iff.mp h1).1
      exact (congrArg Subtype.val h2).symm
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le Z

end Top

/-- Retained-cell incidence with a fixed top.  Accepted carrier epimorphisms
are charged to their complete quotient map through `τ` and one retained
flag; the flag count and the fibre bound are paid together. -/
theorem fusionCarrierAcceptedEpi_card_le_topCells
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop)
    {R A : Type*} [Group R] [Finite R] [Finite A]
    (M : Subgroup R) [M.Normal] (τ : C.quotient →* R ⧸ M)
    (hτ : Function.Surjective τ)
    (flag : FusionCarrierAcceptedEpi C J Accepted → A) (Z : ℕ)
    (h : ∀ (t : J →* R ⧸ M) (a : A),
      Nat.card {γ : FusionCarrierAcceptedEpi C J Accepted //
        τ.comp γ.1.1 = t ∧ flag γ = a} ≤ Z) :
    (Nat.card (FusionCarrierAcceptedEpi C J Accepted) : ℝ) ≤
      (Nat.card A * Z : ℕ) * completeQuotientWeight (R := R) J :=
  fusionCarrierAcceptedEpi_card_le_of_retainedCells C J Accepted
    (fun γ => (fusionCarrierTopQuotientMap M τ hτ γ.1, flag γ)) Z
    (fusionCarrierTopCell_fibre_card_le M τ hτ (fun γ => γ.1) flag Z h)

/-- The literal pullback core determines every retained flag: reading a
flag off the core recovers the flag of the epimorphism which produced it. -/
def fusionCarrierCoreFlag
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop)
    {A : Type*} (flag : FusionCarrierAcceptedEpi C J Accepted → A)
    (H : Subgroup (C.carrier × J)) : Option A :=
  if h : ∃ γ : FusionCarrierAcceptedEpi C J Accepted,
      fusionCarrierSubdirectGraph C J γ.1 = H then
    some (flag (Classical.choose h))
  else none

theorem fusionCarrierCoreFlag_core
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop)
    {A : Type*} (flag : FusionCarrierAcceptedEpi C J Accepted → A)
    (γ : FusionCarrierAcceptedEpi C J Accepted) :
    fusionCarrierCoreFlag C J Accepted flag
        (fusionCarrierSubdirectGraph C J γ.1) = some (flag γ) := by
  have h : ∃ δ : FusionCarrierAcceptedEpi C J Accepted,
      fusionCarrierSubdirectGraph C J δ.1 =
        fusionCarrierSubdirectGraph C J γ.1 := ⟨γ, rfl⟩
  unfold fusionCarrierCoreFlag
  rw [dif_pos h]
  have hγ : Classical.choose h = γ :=
    Subtype.ext (fusionCarrierSubdirectGraph_injective C J
      (Classical.choose_spec h))
  rw [hγ]

/-! ### One abelian layer -/

section Layer

variable {k J Q B : Type} [CommRing k] [Group J] [Group Q] [Group B]

/-- The literal restriction value of a lift, measured against one base lift
of the same bottom map.  By proof irrelevance the base depends only on the
bottom map, not on the lift being measured. -/
def liftRestrictionValue (π : Q →* B) (δ : J →* B) (A : Rep k B)
    (E : OriginalKernelModuleChart π A) (f : HomomorphicLift π δ) :
    LinearMap.range (quotientCocycleRestriction δ A) :=
  ⟨quotientCocycleRestriction δ A
      (homomorphicLiftModuleCocycleEquiv π δ A E
        (Classical.choice (⟨f⟩ : Nonempty (HomomorphicLift π δ))) f),
    _, rfl⟩

/-- Fixing the bottom map and the literal restriction value leaves only the
inflated cocycles of the layer. -/
theorem liftRestrictionValue_fibre_card_le [Finite J] [Finite Q]
    (π : Q →* B) (δ : J →* B) (hδ : Function.Surjective δ)
    (A : Rep k B) [Finite A] (E : OriginalKernelModuleChart π A)
    (y : LinearMap.range (quotientCocycleRestriction δ A)) :
    Nat.card {f : HomomorphicLift π δ // liftRestrictionValue π δ A E f = y} ≤
      Nat.card (cocycles₁ A) := by
  by_cases hne : Nonempty
      {f : HomomorphicLift π δ // liftRestrictionValue π δ A E f = y}
  · obtain ⟨f₁⟩ := hne
    let z := homomorphicLiftModuleCocycleEquiv π δ A E
      (Classical.choice (⟨f₁.1⟩ : Nonempty (HomomorphicLift π δ)))
    have hker : ∀ f : {f : HomomorphicLift π δ //
        liftRestrictionValue π δ A E f = y},
        z f.1 - z f₁.1 ∈ LinearMap.ker (quotientCocycleRestriction δ A) := by
      intro f
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact (congrArg Subtype.val f.2).trans (congrArg Subtype.val f₁.2).symm
    calc
      Nat.card {f : HomomorphicLift π δ // liftRestrictionValue π δ A E f = y} ≤
          Nat.card (LinearMap.ker (quotientCocycleRestriction δ A)) :=
        Nat.card_le_card_of_injective (fun f => ⟨z f.1 - z f₁.1, hker f⟩) (by
          intro f g hfg
          apply Subtype.ext
          apply z.injective
          exact sub_left_inj.mp (congrArg Subtype.val hfg))
      _ = Nat.card (cocycles₁ A) :=
        Nat.card_congr (quotientCocycleRestrictionKernelEquiv δ hδ A)
  · rw [not_nonempty_iff] at hne
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- The literal restriction value, recorded as an index below a supplied
bound on the literal restriction range. -/
def liftRestrictionIndex [Finite J] (π : Q →* B) (δ : J →* B)
    (A : Rep k B) [Finite A] (E : OriginalKernelModuleChart π A) (K : ℕ)
    (hK : Nat.card (LinearMap.range (quotientCocycleRestriction δ A)) ≤ K)
    (f : HomomorphicLift π δ) : Fin K :=
  Fin.castLE hK (Finite.equivFin _ (liftRestrictionValue π δ A E f))

theorem liftRestrictionIndex_congr [Finite J] (π : Q →* B) {δ₁ δ₂ : J →* B}
    (hδ : δ₁ = δ₂) (A : Rep k B) [Finite A] (E : OriginalKernelModuleChart π A)
    (K : ℕ) (hK₁ : Nat.card (LinearMap.range (quotientCocycleRestriction δ₁ A)) ≤ K)
    (hK₂ : Nat.card (LinearMap.range (quotientCocycleRestriction δ₂ A)) ≤ K)
    (f : J →* Q) (h₁ : π.comp f = δ₁) (h₂ : π.comp f = δ₂) :
    liftRestrictionIndex π δ₁ A E K hK₁ ⟨f, h₁⟩ =
      liftRestrictionIndex π δ₂ A E K hK₂ ⟨f, h₂⟩ := by
  subst hδ
  rfl

/-- Fixing the bottom map and the restriction index leaves at most the
inflated cocycles of the layer; an index outside the literal range has an
empty fibre. -/
theorem liftRestrictionIndex_fibre_card_le [Finite J] [Finite Q]
    (π : Q →* B) (δ : J →* B) (hδ : Function.Surjective δ)
    (A : Rep k B) [Finite A] (E : OriginalKernelModuleChart π A) (K : ℕ)
    (hK : Nat.card (LinearMap.range (quotientCocycleRestriction δ A)) ≤ K)
    (i : Fin K) :
    Nat.card {f : HomomorphicLift π δ // liftRestrictionIndex π δ A E K hK f = i} ≤
      Nat.card (cocycles₁ A) := by
  by_cases hne : Nonempty
      {f : HomomorphicLift π δ // liftRestrictionIndex π δ A E K hK f = i}
  · obtain ⟨f₁⟩ := hne
    refine le_trans (Nat.card_le_card_of_injective
      (fun f => (⟨f.1, ?_⟩ : {f : HomomorphicLift π δ //
        liftRestrictionValue π δ A E f = liftRestrictionValue π δ A E f₁.1}))
      ?_) (liftRestrictionValue_fibre_card_le π δ hδ A E _)
    · have hi : liftRestrictionIndex π δ A E K hK f.1 =
          liftRestrictionIndex π δ A E K hK f₁.1 := f.2.trans f₁.2.symm
      exact (Finite.equivFin _).injective (Fin.castLE_injective hK hi)
    · intro f g hfg
      have hfg' := congrArg Subtype.val hfg
      exact Subtype.ext hfg'
  · rw [not_nonempty_iff] at hne
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- The literal restriction range bounded uniformly over every bottom map
from the complete source. -/
def layerFlagBound (J : Type) [Group J] [Finite J] [Finite B]
    (A : Rep k B) [Finite A] : ℕ :=
  letI : Finite (J →* B) :=
    Finite.of_injective (fun f : J →* B => (f : J → B)) DFunLike.coe_injective
  letI : Fintype (J →* B) := Fintype.ofFinite _
  Finset.univ.sup
    (fun δ : J →* B => Nat.card (LinearMap.range (quotientCocycleRestriction δ A)))

theorem card_range_le_layerFlagBound [Finite J] [Finite B]
    (A : Rep k B) [Finite A] (δ : J →* B) :
    Nat.card (LinearMap.range (quotientCocycleRestriction δ A)) ≤
      layerFlagBound J A := by
  letI : Finite (J →* B) :=
    Finite.of_injective (fun f : J →* B => (f : J → B)) DFunLike.coe_injective
  letI : Fintype (J →* B) := Fintype.ofFinite _
  unfold layerFlagBound
  exact Finset.le_sup (f := fun δ : J →* B =>
    Nat.card (LinearMap.range (quotientCocycleRestriction δ A))) (Finset.mem_univ δ)

end Layer

end SymmetricSubgroupAsymptotics

end
