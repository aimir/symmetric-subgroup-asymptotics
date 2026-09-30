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

/-! ### Towers of abelian layers -/

/-- A tower of abelian layers from a carrier quotient `Q` down to the fixed
top `T = R/M`.  Every layer is a surjection whose literal kernel is charted
as a module over the next group, with the original conjugation action; no
layer is split and no nonabelian chief factor occurs. -/
inductive AbelianYonedaTower (T : Type) [Group T] :
    (Q : Type) → [Group Q] → (Q →* T) → Type 1 where
  | base : AbelianYonedaTower T T (MonoidHom.id T)
  | layer {Q B : Type} [Group Q] [Group B] [Finite B]
      (π : Q →* B) (hπ : Function.Surjective π)
      (k : Type) [CommRing k] (A : Rep k B) [Finite A]
      (E : OriginalKernelModuleChart π A)
      {τ : B →* T} (below : AbelianYonedaTower T B τ) :
      AbelianYonedaTower T Q (τ.comp π)

namespace AbelianYonedaTower

variable {T : Type} [Group T]

/-- The composite top of a tower is onto. -/
theorem top_surjective : {Q : Type} → [Group Q] → {τ : Q →* T} →
    AbelianYonedaTower T Q τ → Function.Surjective τ
  | _, _, _, .base => Function.surjective_id
  | _, _, _, @layer _ _ _ _ _ _ _ _ hπ _ _ _ _ _ _ below =>
      (top_surjective below).comp hπ

/-- The retained flag: one literal restriction index at every layer. -/
def Flag (J : Type) [Group J] [Finite J] : {Q : Type} → [Group Q] →
    {τ : Q →* T} → AbelianYonedaTower T Q τ → Type
  | _, _, _, .base => Unit
  | _, _, _, @layer _ _ _ B _ _ _ _ _ _ _ A _ _ _ below =>
      Flag J below × Fin (layerFlagBound J A)

instance flag_finite (J : Type) [Group J] [Finite J] : {Q : Type} → [Group Q] →
    {τ : Q →* T} → (t : AbelianYonedaTower T Q τ) → Finite (Flag J t)
  | _, _, _, .base => inferInstanceAs (Finite Unit)
  | _, _, _, @layer _ _ _ B _ _ _ _ _ _ _ A _ _ _ below =>
      haveI := flag_finite J below
      inferInstanceAs (Finite (Flag J below × Fin (layerFlagBound J A)))

/-- The retained flag of a map to the carrier quotient: the flag of its image
below each layer, together with the literal restriction index of the layer. -/
def flag (J : Type) [Group J] [Finite J] : {Q : Type} → [Group Q] →
    {τ : Q →* T} → (t : AbelianYonedaTower T Q τ) → (J →* Q) → Flag J t
  | _, _, _, .base, _ => ()
  | _, _, _, @layer _ _ _ B _ _ _ π _ _ _ A _ E _ below, γ =>
      (flag J below (π.comp γ),
        liftRestrictionIndex π (π.comp γ) A E (layerFlagBound J A)
          (card_range_le_layerFlagBound A (π.comp γ)) ⟨γ, rfl⟩)

/-- The Yoneda fibre bound `∏ |B¹(B_ℓ,A_ℓ)| |H¹(B_ℓ,A_ℓ)|`. -/
def bound : {Q : Type} → [Group Q] → {τ : Q →* T} →
    AbelianYonedaTower T Q τ → ℕ
  | _, _, _, .base => 1
  | _, _, _, @layer _ _ _ B _ _ _ _ _ _ _ A _ _ _ below =>
      bound below * (Nat.card (coboundaries₁ A) * Nat.card (H1 A))

/-- The joint capacity `∏ |im res_ℓ| |A_ℓ| |H¹(B_ℓ,A_ℓ)|`, with the literal
restriction range bounded uniformly over the complete source. -/
def capacity (J : Type) [Group J] [Finite J] : {Q : Type} → [Group Q] →
    {τ : Q →* T} → AbelianYonedaTower T Q τ → ℕ
  | _, _, _, .base => 1
  | _, _, _, @layer _ _ _ B _ _ _ _ _ _ _ A _ _ _ below =>
      capacity J below * (layerFlagBound J A * (Nat.card A * Nat.card (H1 A)))

/-- The flag count and the Yoneda fibre bound are charged together. -/
theorem card_flag_mul_bound_le_capacity (J : Type) [Group J] [Finite J] :
    {Q : Type} → [Group Q] → {τ : Q →* T} → (t : AbelianYonedaTower T Q τ) →
    Nat.card (Flag J t) * bound t ≤ capacity J t
  | _, _, _, .base => by
      simp [Flag, bound, capacity]
  | _, _, _, @layer _ _ _ B _ _ _ _ _ _ _ A _ _ _ below => by
      have ih := card_flag_mul_bound_le_capacity J below
      have hB : Nat.card (coboundaries₁ A) ≤ Nat.card A := coboundaries_card_le A
      change Nat.card (Flag J below × Fin (layerFlagBound J A)) *
          (bound below * (Nat.card (coboundaries₁ A) * Nat.card (H1 A))) ≤
        capacity J below * (layerFlagBound J A * (Nat.card A * Nat.card (H1 A)))
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
      calc Nat.card (Flag J below) * layerFlagBound J A *
            (bound below * (Nat.card (coboundaries₁ A) * Nat.card (H1 A))) =
          (Nat.card (Flag J below) * bound below) *
            (layerFlagBound J A * (Nat.card (coboundaries₁ A) * Nat.card (H1 A))) := by
            ring
        _ ≤ capacity J below * (layerFlagBound J A * (Nat.card A * Nat.card (H1 A))) :=
            Nat.mul_le_mul ih (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hB))

/-- The Yoneda fibre of a fixed top map and a fixed retained flag has at most
`bound` members.  At each layer the fibre over one bottom map and one
restriction index consists of inflated cocycles only. -/
theorem fibre_card_le (J : Type) [Group J] [Finite J] :
    {Q : Type} → [Group Q] → [Finite Q] →
    {τ : Q →* T} → (t : AbelianYonedaTower T Q τ) →
    ∀ (top : J →* T) (a : Flag J t),
      Nat.card {γ : GroupEpimorphism J Q //
        τ.comp γ.1 = top ∧ flag J t γ.1 = a} ≤ bound t
  | _, _, _, _, .base, top, a => by
      change Nat.card {γ : GroupEpimorphism J T //
        (MonoidHom.id T).comp γ.1 = top ∧ flag J .base γ.1 = a} ≤ 1
      apply Finite.card_le_one_iff_subsingleton.mpr
      constructor
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      rw [← MonoidHom.id_comp x.1.1, ← MonoidHom.id_comp y.1.1, x.2.1, y.2.1]
  | Q, _, _, _, @layer _ _ _ B _ _ _ π hπ k _ A _ E τ below, top, a => by
      let K := layerFlagBound J A
      let S := {γ : GroupEpimorphism J Q //
        (τ.comp π).comp γ.1 = top ∧
          flag J (.layer π hπ k A E below) γ.1 = a}
      let SB := {δ : GroupEpimorphism J B //
        τ.comp δ.1 = top ∧ flag J below δ.1 = a.1}
      let F : S → SB := fun γ =>
        ⟨⟨π.comp γ.1.1, hπ.comp γ.1.2⟩,
          (MonoidHom.comp_assoc γ.1.1 π τ).symm.trans γ.2.1,
          congrArg Prod.fst γ.2.2⟩
      have hfibre : ∀ δ : SB, Nat.card {γ : S // F γ = δ} ≤
          Nat.card (cocycles₁ A) := by
        intro δ
        refine le_trans (Nat.card_le_card_of_injective
          (fun γ => (⟨⟨γ.1.1.1, congrArg (fun d : SB => d.1.1) γ.2⟩, ?_⟩ :
            {f : HomomorphicLift π δ.1.1 //
              liftRestrictionIndex π δ.1.1 A E K
                (card_range_le_layerFlagBound A δ.1.1) f = a.2})) ?_)
          (liftRestrictionIndex_fibre_card_le π δ.1.1 δ.1.2 A E K
            (card_range_le_layerFlagBound A δ.1.1) a.2)
        · have hδ : π.comp γ.1.1.1 = δ.1.1 := congrArg (fun d : SB => d.1.1) γ.2
          exact (liftRestrictionIndex_congr π hδ A E K
            (card_range_le_layerFlagBound A (π.comp γ.1.1.1))
            (card_range_le_layerFlagBound A δ.1.1) γ.1.1.1 rfl hδ).symm.trans
              (congrArg Prod.snd γ.1.2.2)
        · intro γ γ' h
          have h' := congrArg (fun f => f.1.1) h
          exact Subtype.ext (Subtype.ext (Subtype.ext h'))
      have hS := natCard_le_uniformFiber_mul F (Nat.card (cocycles₁ A)) hfibre
      have hSB : Nat.card SB ≤ bound below := fibre_card_le J below top a.1
      change Nat.card S ≤ bound below *
        (Nat.card (coboundaries₁ A) * Nat.card (H1 A))
      rw [← cocycles_card_eq_coboundaries_mul_H1 A]
      calc Nat.card S ≤ Nat.card (cocycles₁ A) * Nat.card SB := hS
        _ ≤ Nat.card (cocycles₁ A) * bound below := Nat.mul_le_mul_left _ hSB
        _ = bound below * Nat.card (cocycles₁ A) := Nat.mul_comm _ _

end AbelianYonedaTower

/-- Annihilator-aware Yoneda incidence on a reversible carrier.  The complete
quotient map uses the tower's fixed top; the flag is the tower's literal
restriction flag, a function of the literal pullback core; and the flag
count and Yoneda fibre bound are charged jointly by the tower capacity. -/
theorem fusionCarrierAcceptedEpi_card_le_abelianTower
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (C.carrier × Equiv.Perm (Fin b)) → Prop)
    {R : Type} [Group R] [Finite R] (M : Subgroup R) [M.Normal]
    {τ : C.quotient →* R ⧸ M}
    (t : AbelianYonedaTower (R ⧸ M) C.quotient τ) :
    (Nat.card (FusionCarrierAcceptedEpi C J Accepted) : ℝ) ≤
      (t.capacity J : ℝ) * completeQuotientWeight (R := R) J := by
  have h := fusionCarrierAcceptedEpi_card_le_topCells C J Accepted M τ
    t.top_surjective (fun γ => t.flag J γ.1.1) (t.bound) (by
      intro top a
      refine le_trans (Nat.card_le_card_of_injective
        (fun γ => (⟨γ.1.1, γ.2⟩ : {γ : GroupEpimorphism J C.quotient //
          τ.comp γ.1 = top ∧ t.flag J γ.1 = a})) ?_) (t.fibre_card_le J top a)
      intro γ γ' hγ
      have hγ' := congrArg Subtype.val hγ
      simp only at hγ'
      exact Subtype.ext (Subtype.ext hγ'))
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (completeQuotientWeight_nonneg J))
  exact_mod_cast t.card_flag_mul_bound_le_capacity J

end SymmetricSubgroupAsymptotics

end
