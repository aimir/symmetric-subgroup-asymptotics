import SymmetricSubgroupAsymptotics.SubgroupTailFibre
import Mathlib.GroupTheory.Abelianization.Defs

/-! Exact quotient graphs over an arbitrary abelian first factor.
The second image is the literal original subgroup, and the first image
need not be full. This proves the algebraic double-sum identity used in
the Hall-mixture argument; it does not assert the Hall subgroup formula
or a numerical bound for subgroups of an arbitrary finite p-group.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.AbelianProductGraphClassification

variable {E B : Type*} [CommGroup E] [Group B]

abbrev FullSecond (E B : Type*) [Group E] [Group B] :=
  {H : Subgroup (E × B) // H.map (MonoidHom.snd E B) = ⊤}

private def second (H : FullSecond E B) : H.1 →* B :=
  (MonoidHom.snd E B).comp H.1.subtype

private theorem second_surjective (H : FullSecond E B) :
    Function.Surjective (second H) := by
  intro b
  have hb : b ∈ H.1.map (MonoidHom.snd E B) := by rw [H.2]; trivial
  obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp hb
  exact ⟨⟨x,hx⟩,he⟩

private def firstQuotient (H : FullSecond E B) : H.1 →* E ⧸ H.1.goursatFst :=
  (QuotientGroup.mk' H.1.goursatFst).comp ((MonoidHom.fst E B).comp H.1.subtype)

private theorem second_ker_le (H : FullSecond E B) :
    (second H).ker ≤ (firstQuotient H).ker := by
  intro x hx
  have hs : x.1.2 = 1 := hx
  apply (QuotientGroup.eq_one_iff (N := H.1.goursatFst) _).mpr
  apply Subgroup.mem_goursatFst.mpr
  simpa only [← hs] using x.2

/-- The actual quotient map on the entire second factor. It need not be onto. -/
def quotientCharacter (H : FullSecond E B) : B →* E ⧸ H.1.goursatFst :=
  (second H).liftOfSurjective (second_surjective H) ⟨firstQuotient H,second_ker_le H⟩

@[simp] theorem quotientCharacter_apply (H : FullSecond E B) (x : H.1) :
    quotientCharacter H x.1.2 = QuotientGroup.mk' H.1.goursatFst x.1.1 :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- A literal graph modulo K inside the original product. -/
def quotientGraph (K : Subgroup E) (f : B →* E ⧸ K) : Subgroup (E × B) where
  carrier := {x | QuotientGroup.mk' K x.1 = f x.2}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change QuotientGroup.mk' K (x.1*y.1) = f (x.2*y.2)
    rw [map_mul,map_mul,hx,hy]
  inv_mem' := by
    intro x hx
    change QuotientGroup.mk' K x.1⁻¹ = f x.2⁻¹
    rw [map_inv,map_inv,hx]

@[simp] theorem mem_quotientGraph (K : Subgroup E) (f : B →* E ⧸ K) (x : E × B) :
    x ∈ quotientGraph K f ↔ QuotientGroup.mk' K x.1 = f x.2 := Iff.rfl

theorem quotientGraph_full (K : Subgroup E) (f : B →* E ⧸ K) :
    (quotientGraph K f).map (MonoidHom.snd E B) = ⊤ := by
  apply top_unique
  intro b _
  obtain ⟨e,he⟩ := QuotientGroup.mk'_surjective K (f b)
  exact Subgroup.mem_map.mpr ⟨(e,b),he,rfl⟩

@[simp] theorem quotientGraph_axis (K : Subgroup E) (f : B →* E ⧸ K) :
    (quotientGraph K f).goursatFst = K := by
  ext e
  rw [Subgroup.mem_goursatFst,mem_quotientGraph,map_one]
  exact QuotientGroup.eq_one_iff e

theorem quotientCharacter_recovers (H : FullSecond E B) :
    quotientGraph H.1.goursatFst (quotientCharacter H) = H.1 := by
  ext x
  rw [mem_quotientGraph]
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := second_surjective H x.2
    change y.1.2 = x.2 at hy
    have hq : QuotientGroup.mk' H.1.goursatFst x.1 =
        QuotientGroup.mk' H.1.goursatFst y.1.1 :=
      hx.trans ((congrArg (quotientCharacter H) hy).symm.trans (quotientCharacter_apply H y))
    have ha : x.1*y.1.1⁻¹ ∈ H.1.goursatFst := by
      apply (QuotientGroup.eq_one_iff (N := H.1.goursatFst) _).mp
      change QuotientGroup.mk' H.1.goursatFst (x.1*y.1.1⁻¹) = 1
      rw [map_mul,map_inv,hq,mul_inv_cancel]
    have hm := H.1.mul_mem (Subgroup.mem_goursatFst.mp ha) y.2
    have he : (x.1*y.1.1⁻¹,(1 : B))*y.1 = x := by
      apply Prod.ext
      · simp
      · simpa only [Prod.snd_mul,one_mul] using hy
    exact he ▸ hm
  · intro hx
    exact (quotientCharacter_apply H ⟨x,hx⟩).symm

private def parameterMap : (Σ K : Subgroup E, B →* E ⧸ K) → FullSecond E B :=
  fun d => ⟨quotientGraph d.1 d.2,quotientGraph_full d.1 d.2⟩

private theorem parameterMap_injective :
    Function.Injective (parameterMap (E := E) (B := B)) := by
  rintro ⟨K,f⟩ ⟨K',f'⟩ he
  have hgraph : quotientGraph K f = quotientGraph K' f' := congrArg Subtype.val he
  have hK := congrArg Subgroup.goursatFst hgraph
  simp only [quotientGraph_axis] at hK
  subst K'
  have hf : f = f' := by
    apply MonoidHom.ext
    intro b
    obtain ⟨e,he⟩ := QuotientGroup.mk'_surjective K (f b)
    have hm : (e,b) ∈ quotientGraph K f := he
    rw [hgraph,mem_quotientGraph] at hm
    exact he.symm.trans hm
  subst f'
  rfl

private theorem parameterMap_surjective :
    Function.Surjective (parameterMap (E := E) (B := B)) := by
  intro H
  exact ⟨⟨H.1.goursatFst,quotientCharacter H⟩,Subtype.ext (quotientCharacter_recovers H)⟩

/-- All second-full subgroups are classified without requiring first fullness. -/
def fullClassification : FullSecond E B ≃ (Σ K : Subgroup E, B →* E ⧸ K) :=
  (Equiv.ofBijective parameterMap ⟨parameterMap_injective,parameterMap_surjective⟩).symm

@[simp] theorem fullClassification_symm (K : Subgroup E) (f : B →* E ⧸ K) :
    ((fullClassification (E := E) (B := B)).symm ⟨K,f⟩).1 = quotientGraph K f := rfl

private def unrestrictedTailEquiv :
    SubgroupTailFibre.CoreFamily (A := E) (B := B) (fun _ => True) (fun _ => True) ≃
      (Σ L : Subgroup B, FullSecond E L) :=
  Equiv.sigmaCongr (Equiv.subtypeUnivEquiv (fun _ => True.intro)) (fun _ =>
    { toFun := fun H => ⟨H.1,H.2.1⟩
      invFun := fun H => ⟨H.1,H.2,True.intro⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })

/-- The complete actual tail is retained before choosing its quotient graph. -/
def tailClassification : Subgroup (E × B) ≃ (Σ L : Subgroup B, FullSecond E L) :=
  ((Equiv.subtypeUnivEquiv
      (fun _ : Subgroup (E × B) => (⟨True.intro,True.intro⟩ : True ∧ True))).symm.trans
    (SubgroupTailFibre.equiv (fun _ => True) (fun _ => True))).trans unrestrictedTailEquiv

/-- Exact original product classification. No quotient-automorphism divisor occurs. -/
def classification : Subgroup (E × B) ≃
    (Σ L : Subgroup B, Σ K : Subgroup E, L →* E ⧸ K) :=
  tailClassification.trans (Equiv.sigmaCongrRight fun _ => fullClassification)

/-- Any predicate on the original subgroup is evaluated on its exact inverse. -/
def restrictedClassification (P : Subgroup (E × B) → Prop) :
    {H : Subgroup (E × B) // P H} ≃
      {d : (Σ L : Subgroup B, Σ K : Subgroup E, L →* E ⧸ K) //
        P (classification.symm d)} :=
  classification.subtypeEquivOfSubtype' (p := P)

section Finite
variable [Finite E] [Finite B]

local instance subgroupFinite {G : Type*} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

local instance homFinite {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q] :
    Finite (G →* Q) :=
  Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

local instance quotientFinite (K : Subgroup E) : Finite (E ⧸ K) :=
  Finite.of_surjective (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)

attribute [local instance] Fintype.ofFinite

/-- The exact double sum used in the Hall-mixture argument. -/
theorem card_eq_sum_hom :
    Nat.card (Subgroup (E × B)) =
      ∑ L : Subgroup B, ∑ K : Subgroup E, Nat.card (L →* E ⧸ K) := by
  rw [Nat.card_congr (classification (E := E) (B := B)),Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro L _
  exact Nat.card_sigma

/-- For each fixed actual tail, its Hom sum is a subfamily of subgroups
of E times the tail's complete abelianization, not its binary quotient. -/
theorem sum_hom_le_abelianization_subgroups :
    (∑ K : Subgroup E, Nat.card (B →* E ⧸ K)) ≤
      Nat.card (Subgroup (E × Abelianization B)) := by
  letI : Finite (Abelianization B) :=
    Finite.of_surjective (Abelianization.of : B →* Abelianization B)
      (QuotientGroup.mk'_surjective (commutator B))
  let e : (Σ K : Subgroup E, B →* E ⧸ K) ≃ FullSecond E (Abelianization B) :=
    (Equiv.sigmaCongrRight (fun _ => Abelianization.lift)).trans fullClassification.symm
  rw [← Nat.card_sigma]
  exact Nat.card_le_card_of_injective (fun d => (e d).1)
    (Subtype.val_injective.comp e.injective)

end Finite
end SymmetricSubgroupAsymptotics.AbelianProductGraphClassification
