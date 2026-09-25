import SymmetricSubgroupAsymptotics.FusionLabelCounting
import SymmetricSubgroupAsymptotics.FusionGoursatCount
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Literal distinguished-orbit pointing and deletion

The complete complement is an arbitrary permutation subgroup. The original
normalizer acts on the actual orbit axis and the whole complement together.
This proves the original factorial weight for any invariant accepted local
family, before choosing a hot/cold estimate for its surviving Goursat fibres.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {Ω Z : Type*} (U : Subgroup (Equiv.Perm Ω))

/-- The original orbit and the untouched complete complement act on their
literal disjoint physical point sets. -/
def fusionOrbitAction : U × Equiv.Perm Z →* Equiv.Perm (Ω ⊕ Z) :=
  (Equiv.Perm.sumCongrHom Ω Z).comp (U.subtype.prodMap (MonoidHom.id _))

theorem fusionOrbitAction_injective : Function.Injective (fusionOrbitAction (Z := Z) U) := by
  intro x y he
  have h := Equiv.Perm.sumCongrHom_injective he
  change ((x.1 : Equiv.Perm Ω),x.2)=((y.1 : Equiv.Perm Ω),y.2) at h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
    (congrArg (fun z : Equiv.Perm Ω × Equiv.Perm Z => z.2) h)

/-- An original coordinate change conjugates both parts of the actual
subgroup. The axis may move under the original normalizer. -/
def fusionOrbitCoordinateChange
    (c : Subgroup.normalizer (U : Set (Equiv.Perm Ω)) × Equiv.Perm Z) :
    (U × Equiv.Perm Z) ≃* (U × Equiv.Perm Z) :=
  (U.normalizerMonoidHom c.1).prodCongr (MulAut.conj c.2)

theorem fusionOrbitAction_coordinateChange
    (c : Subgroup.normalizer (U : Set (Equiv.Perm Ω)) × Equiv.Perm Z)
    (x : U × Equiv.Perm Z) :
    fusionOrbitAction U (fusionOrbitCoordinateChange U c x) =
      (fusionPointingSymmetryMap U c).permCongr (fusionOrbitAction U x) := by
  apply Equiv.ext
  rintro (a|z) <;> rfl

theorem fusionOrbitAction_map_coordinateChange
    (c : Subgroup.normalizer (U : Set (Equiv.Perm Ω)) × Equiv.Perm Z)
    (H : Subgroup (U × Equiv.Perm Z)) :
    (H.map (fusionOrbitCoordinateChange U c).toMonoidHom).map (fusionOrbitAction U) =
      relabelSubgroup (fusionPointingSymmetryMap U c) (H.map (fusionOrbitAction U)) := by
  change _ = (H.map (fusionOrbitAction U)).map
    (fusionPointingSymmetryMap U c).permCongrHom.toMonoidHom
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  exact fusionOrbitAction_coordinateChange U c

/-- Naturality is a structural coordinate-change condition on the actual
accepted local family. It contains no counting estimate. -/
def FusionOrbitNatural (P : Subgroup (U × Equiv.Perm Z) → Prop) : Prop :=
  ∀ c : Subgroup.normalizer (U : Set (Equiv.Perm Ω)) × Equiv.Perm Z,
    ∀ H, P H → P (H.map (fusionOrbitCoordinateChange U c).toMonoidHom)

/-- Literal local permutation models, keeping the complete complement. -/
def FusionOrbitModel (P : Subgroup (U × Equiv.Perm Z) → Prop) :
    Set (Subgroup (Equiv.Perm (Ω ⊕ Z))) :=
  Set.range (fun H : {H // P H} => H.1.map (fusionOrbitAction U))

/-- Physical subgroups admitting the indicated original orbit model. -/
def FusionOrbitFamily (P : Subgroup (U × Equiv.Perm Z) → Prop) :=
  FusionLabelledFamily (FusionOrbitModel U P)

theorem fusionOrbitModel_card (P : Subgroup (U × Equiv.Perm Z) → Prop) :
    Nat.card (FusionOrbitModel U P) = Nat.card {H // P H} := by
  exact (Nat.card_congr (Equiv.ofInjective
    (fun H : {H // P H} => H.1.map (fusionOrbitAction U))
    (fun H K he => Subtype.ext ((Subgroup.map_injective
      (fusionOrbitAction_injective U)) he)))).symm

theorem fusionOrbitModel_natural (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (hP : FusionOrbitNatural U P) :
    FusionLabelNatural (fusionPointingSymmetries U) (FusionOrbitModel U P) := by
  rintro s ⟨c,rfl⟩ K ⟨H,rfl⟩
  exact ⟨⟨H.1.map (fusionOrbitCoordinateChange U c).toMonoidHom,hP c H.1 H.2⟩,
    fusionOrbitAction_map_coordinateChange U c H.1⟩

/-- The physical labelled subgroup family has the original action divisor
and the complete-complement factorial, including an empty complement. -/
theorem fusionOrbitFamily_card_le [Fintype Ω] [Fintype Z]
    (P : Subgroup (U × Equiv.Perm Z) → Prop) (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U P) : ℝ) ≤
      ((Fintype.card Ω+Fintype.card Z).factorial : ℝ) /
        ((Fintype.card Z).factorial *
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm Ω))) : ℝ)) *
            Nat.card {H // P H} := by
  have h := fusion_original_pointing_bound U (FusionOrbitModel U P)
    (fusionOrbitModel_natural U P hP)
  have hc : Nat.card {K // FusionOrbitModel U P K}=Nat.card {H // P H} :=
    fusionOrbitModel_card U P
  rw [hc] at h
  exact h

/-- Fullness and transitivity prove that the marked physical block is
an actual orbit of H. No orbit of the complement is removed or summarized. -/
theorem fusionOrbitAction_orbit_eq
    (hU : ∀ x y : Ω, ∃ u : U, (u : Equiv.Perm Ω) x=y)
    (H : FusionFullSubgroups U (Equiv.Perm Z)) (x : Ω) :
    MulAction.orbit (H.1.map (fusionOrbitAction U)) (Sum.inl x) =
      Set.range (Sum.inl : Ω → Ω ⊕ Z) := by
  ext a
  constructor
  · rintro ⟨h,rfl⟩
    obtain ⟨⟨u,v⟩,hu,hh⟩ := h.2
    refine ⟨(u : Equiv.Perm Ω) x,?_⟩
    change Sum.inl ((u : Equiv.Perm Ω) x)=(h : Equiv.Perm (Ω ⊕ Z)) (Sum.inl x)
    rw [← hh]
    rfl
  · rintro ⟨y,rfl⟩
    obtain ⟨u,hu⟩ := hU x y
    have hm : u ∈ H.1.map (MonoidHom.fst U (Equiv.Perm Z)) := by rw [H.2]; trivial
    obtain ⟨⟨v,z⟩,hv,he⟩ := hm
    refine ⟨⟨fusionOrbitAction U (v,z),⟨(v,z),hv,rfl⟩⟩,?_⟩
    change Sum.inl ((v : Equiv.Perm Ω) x)=Sum.inl y
    change v=u at he
    rw [he,hu]

end SymmetricSubgroupAsymptotics
