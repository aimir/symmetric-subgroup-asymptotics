import SymmetricSubgroupAsymptotics.FusionGoursat

/-! Exact original axis and literal epimorphism sums for a pointed orbit. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {U Q G : Type*} [Group U] [Group Q] [Group G]

instance [Finite G] [Finite Q] (J : Subgroup G) : Finite (GroupEpimorphism J Q) :=
  Finite.of_injective (fun f : GroupEpimorphism J Q => (f.1 : J → Q))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))

/-- The full fixed-axis count is a sum over complete complement groups,
with each literal epimorphism counted once. -/
theorem fusionPointedSubgroups_card [Finite G] [Finite Q]
    (π : U →* Q) (hπ : Function.Surjective π) :
    Nat.card (FusionPointedSubgroups π G) =
      ∑ J : Subgroup G, Nat.card (GroupEpimorphism J Q) := by
  rw [Nat.card_congr (fusionGoursatEquiv π hπ)]
  exact Nat.card_sigma

/-- Surviving fibres keep their predicate on the original complete H. -/
def fusionGoursatSurvivalEquiv (π : U →* Q) (hπ : Function.Surjective π)
    (P : FusionPointedSubgroups π G → Prop) :
    {H : FusionPointedSubgroups π G // P H} ≃
      Σ J : Subgroup G, {β : GroupEpimorphism J Q // P (fusionGoursatEncode π ⟨J,β⟩)} :=
  (fusionGoursatRestrictedEquiv π hπ P).trans
    { toFun := fun d => ⟨d.1.1,d.1.2,d.2⟩
      invFun := fun d => ⟨⟨d.1,d.2.1⟩,d.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem fusionPointedSubgroups_survival_card [Finite G] [Finite Q]
    (π : U →* Q) (hπ : Function.Surjective π)
    (P : FusionPointedSubgroups π G → Prop) :
    Nat.card {H : FusionPointedSubgroups π G // P H} =
      ∑ J : Subgroup G,
        Nat.card {β : GroupEpimorphism J Q // P (fusionGoursatEncode π ⟨J,β⟩)} := by
  rw [Nat.card_congr (fusionGoursatSurvivalEquiv π hπ P)]
  exact Nat.card_sigma

/-- All actual full original orbit projections, before selecting an axis. -/
abbrev FusionFullSubgroups (U G : Type*) [Group U] [Group G] :=
  {H : Subgroup (U×G) // H.map (MonoidHom.fst U G)=⊤}

def fusionFullAxis (H : FusionFullSubgroups U G) : {N : Subgroup U // N.Normal} :=
  ⟨H.1.goursatFst,Subgroup.normal_goursatFst (by
    intro u
    have hu : u ∈ H.1.map (MonoidHom.fst U G) := by rw [H.2]; trivial
    obtain ⟨x,hx,he⟩ := hu
    exact ⟨⟨x,hx⟩,he⟩)⟩

instance fusionNormalAxis_normal (N : {N : Subgroup U // N.Normal}) : N.1.Normal := N.2

def fusionAxisForget :
    (Σ N : {N : Subgroup U // N.Normal}, FusionPointedSubgroups (QuotientGroup.mk' N.1) G) →
      FusionFullSubgroups U G := fun d => ⟨d.2.1,d.2.2.1⟩

theorem fusionAxisForget_bijective :
    Function.Bijective (fusionAxisForget (U := U) (G := G)) := by
  constructor
  · rintro ⟨N,H⟩ ⟨M,K⟩ he
    have hH : H.1=K.1 := congrArg Subtype.val he
    have hN : N=M := by
      apply Subtype.ext
      have hHN : H.1.goursatFst=N.1 := by simpa only [QuotientGroup.ker_mk'] using H.2.2
      have hKM : K.1.goursatFst=M.1 := by simpa only [QuotientGroup.ker_mk'] using K.2.2
      exact hHN.symm.trans ((congrArg Subgroup.goursatFst hH).trans hKM)
    subst M
    have hHK : H=K := Subtype.ext hH
    subst K
    rfl
  · intro H
    exact ⟨⟨fusionFullAxis H,H.1,H.2,by rw [QuotientGroup.ker_mk']; rfl⟩,rfl⟩

/-- Every literal axis is counted once, before any original normalizer
division. In particular the normalizer is allowed to move that axis. -/
def fusionAxisEquiv : FusionFullSubgroups U G ≃
    Σ N : {N : Subgroup U // N.Normal}, FusionPointedSubgroups (QuotientGroup.mk' N.1) G :=
  (Equiv.ofBijective fusionAxisForget fusionAxisForget_bijective).symm

/-- The complete literal-normal sum supplies the invariant local count
needed before dividing by the full original action normalizer. -/
theorem fusionFullSubgroups_card [Finite U] [Finite G] :
    Nat.card (FusionFullSubgroups U G) =
      ∑ N : {N : Subgroup U // N.Normal},
        ∑ J : Subgroup G, Nat.card (GroupEpimorphism J (U ⧸ N.1)) := by
  rw [Nat.card_congr (fusionAxisEquiv (U := U) (G := G)),Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro N _
  exact fusionPointedSubgroups_card (QuotientGroup.mk' N.1) (QuotientGroup.mk'_surjective N.1)

/-- Complete literal Goursat parameters, with the original normal first. -/
abbrev FusionFullGoursatData (U G : Type*) [Group U] [Group G] :=
  Σ N : {N : Subgroup U // N.Normal}, Σ J : Subgroup G, GroupEpimorphism J (U ⧸ N.1)

def fusionFullGoursatEquiv : FusionFullSubgroups U G ≃ FusionFullGoursatData U G :=
  fusionAxisEquiv.trans (Equiv.sigmaCongrRight fun N =>
    fusionGoursatEquiv (QuotientGroup.mk' N.1) (QuotientGroup.mk'_surjective N.1))

/-- Decode with the same original quotient and full complement. -/
def fusionFullGoursatEncode (N : {N : Subgroup U // N.Normal})
    (J : Subgroup G) (β : GroupEpimorphism J (U ⧸ N.1)) : FusionFullSubgroups U G :=
  ⟨fusionQuotientGraph (QuotientGroup.mk' N.1) J β.1,
    fusionQuotientGraph_full (QuotientGroup.mk' N.1) J β.1 β.2⟩

@[simp] theorem fusionFullGoursatEquiv_symm (N : {N : Subgroup U // N.Normal})
    (J : Subgroup G) (β : GroupEpimorphism J (U ⧸ N.1)) :
    (fusionFullGoursatEquiv (U := U) (G := G)).symm ⟨N,J,β⟩ =
      fusionFullGoursatEncode N J β := rfl

/-- Exact accepted-family count. The acceptance predicate can refer to any
data of the original subgroup, including future attachments and characters. -/
theorem fusionFullSubgroups_survival_card [Finite U] [Finite G]
    (P : FusionFullSubgroups U G → Prop) :
    Nat.card {H : FusionFullSubgroups U G // P H} =
      ∑ N : {N : Subgroup U // N.Normal}, ∑ J : Subgroup G,
        Nat.card {β : GroupEpimorphism J (U ⧸ N.1) // P (fusionFullGoursatEncode N J β)} := by
  let e := (fusionFullGoursatEquiv (U := U) (G := G)).subtypeEquivOfSubtype' (p := P)
  let e' : {d : FusionFullGoursatData U G // P (fusionFullGoursatEquiv.symm d)} ≃
      (Σ N : {N : Subgroup U // N.Normal}, Σ J : Subgroup G,
        {β : GroupEpimorphism J (U ⧸ N.1) // P (fusionFullGoursatEncode N J β)}) :=
    { toFun := fun d => ⟨d.1.1,d.1.2.1,d.1.2.2,d.2⟩
      invFun := fun d => ⟨⟨d.1,d.2.1,d.2.2.1⟩,d.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e.trans e'),Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro N _
  exact Nat.card_sigma

end SymmetricSubgroupAsymptotics
