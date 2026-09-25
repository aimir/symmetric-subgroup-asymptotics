import SymmetricSubgroupAsymptotics.FusionOrbitPointing

/-!
# Original-weight physical Goursat sum

The axis sum is over literal normal subgroups before division by the
original action normalizer. Survival remains a predicate on the actual
whole subgroup and the entire complement is retained in each summand.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {A G : Type*} [Group A] [Group G]

/-- Full projection is preserved by actual independent coordinate changes. -/
theorem fusion_full_map_prod (H : Subgroup (A × G))
    (hH : H.map (MonoidHom.fst A G)=⊤) (e : A ≃* A) (f : G ≃* G) :
    (H.map (e.prodCongr f).toMonoidHom).map (MonoidHom.fst A G)=⊤ := by
  rw [Subgroup.map_map]
  have he : (MonoidHom.fst A G).comp (e.prodCongr f).toMonoidHom =
      e.toMonoidHom.comp (MonoidHom.fst A G) := by ext x; rfl
  rw [he,← Subgroup.map_map,hH]
  exact Subgroup.map_top_of_surjective _ e.surjective

/-- The actual intersection axis moves by the original first-coordinate
automorphism. It is not silently assumed to be normalizer-fixed. -/
theorem fusion_axis_map_prod (H : Subgroup (A × G)) (e : A ≃* A) (f : G ≃* G) :
    (H.map (e.prodCongr f).toMonoidHom).goursatFst = H.goursatFst.map e.toMonoidHom := by
  ext a
  rw [Subgroup.mem_goursatFst]
  constructor
  · rintro ⟨⟨x,y⟩,hxy,he⟩
    have hx : e x=a := congrArg Prod.fst he
    have hy : f y=1 := congrArg (fun z : A×G => z.2) he
    have hy' : y=1 := f.injective (hy.trans f.map_one.symm)
    subst y
    exact ⟨x,Subgroup.mem_goursatFst.mpr hxy,hx⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨(x,1),Subgroup.mem_goursatFst.mp hx,by simpa using Prod.ext he f.map_one⟩

/-- The whole complement is transported, including all its correlations. -/
theorem fusion_complement_map_prod (H : Subgroup (A × G)) (e : A ≃* A) (f : G ≃* G) :
    (H.map (e.prodCongr f).toMonoidHom).map (MonoidHom.snd A G) =
      (H.map (MonoidHom.snd A G)).map f.toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1

variable {Ω Z : Type*} (U : Subgroup (Equiv.Perm Ω))

theorem fusionOrbitNatural_full :
    FusionOrbitNatural (Z := Z) U (fun H => H.map (MonoidHom.fst U (Equiv.Perm Z))=⊤) := by
  intro c H hH
  exact fusion_full_map_prod H hH (U.normalizerMonoidHom c.1) (MulAut.conj c.2)

theorem fusionOrbitNatural_and (P R : Subgroup (U × Equiv.Perm Z) → Prop)
    (hP : FusionOrbitNatural U P) (hR : FusionOrbitNatural U R) :
    FusionOrbitNatural U (fun H => P H ∧ R H) := by
  intro c H hH
  exact ⟨hP c H hH.1,hR c H hH.2⟩

/-- Axis acceptance must be stable under the full original normalizer.
This is a structural condition on a menu, not a numerical hypothesis. -/
theorem fusionOrbitNatural_axis
    (Accept : Subgroup U → Prop)
    (hAccept : ∀ c : Subgroup.normalizer (U : Set (Equiv.Perm Ω)),
      ∀ N, Accept N → Accept (N.map (U.normalizerMonoidHom c).toMonoidHom)) :
    FusionOrbitNatural (Z := Z) U (fun H => Accept H.goursatFst) := by
  intro c H hH
  change Accept ((H.map ((U.normalizerMonoidHom c.1).prodCongr
    (MulAut.conj c.2)).toMonoidHom).goursatFst)
  rw [fusion_axis_map_prod]
  exact hAccept c.1 H.goursatFst hH

/-- A conjugacy-invariant hot/cold test uses the complete actual source. -/
theorem fusionOrbitNatural_source
    (P : Subgroup (Equiv.Perm Z) → Prop)
    (hP : ∀ c : Equiv.Perm Z, ∀ J, P J → P (J.map (MulAut.conj c).toMonoidHom)) :
    FusionOrbitNatural U (fun H => P (H.map (MonoidHom.snd U (Equiv.Perm Z)))) := by
  intro c H hH
  change P ((H.map ((U.normalizerMonoidHom c.1).prodCongr
    (MulAut.conj c.2)).toMonoidHom).map (MonoidHom.snd U (Equiv.Perm Z)))
  rw [fusion_complement_map_prod]
  exact hP c.2 _ hH

/-- A full physical local model retaining arbitrary original survival. -/
def FusionAcceptedOrbitPredicate (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (H : Subgroup (U × Equiv.Perm Z)) : Prop :=
  H.map (MonoidHom.fst U (Equiv.Perm Z))=⊤ ∧ P H

/-- Exact regrouping of accepted full local subgroups, with no information
loss or quotient-automorphism division. -/
theorem fusionAcceptedOrbit_card [Finite Ω] [Finite Z]
    (P : Subgroup (U × Equiv.Perm Z) → Prop) :
    Nat.card {H // FusionAcceptedOrbitPredicate U P H} =
      ∑ N : {N : Subgroup U // N.Normal}, ∑ J : Subgroup (Equiv.Perm Z),
        Nat.card {β : GroupEpimorphism J (U ⧸ N.1) //
          P (fusionFullGoursatEncode N J β).1} := by
  let e : {H // FusionAcceptedOrbitPredicate U P H} ≃
      {H : FusionFullSubgroups U (Equiv.Perm Z) // P H.1} :=
    { toFun := fun H => ⟨⟨H.1,H.2.1⟩,H.2.2⟩
      invFun := fun H => ⟨H.1.1,H.1.2,H.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact fusionFullSubgroups_survival_card (fun H => P H.1)

/-- The physical original-weight bound. Every axis is counted before
normalizer division; every complement and surviving actual quotient map
is counted literally. Earlier owner exclusions or later continuation can
be retained in P whenever the actual accepted family is natural. -/
theorem fusionPhysical_original_weight [Fintype Ω] [Fintype Z]
    (P : Subgroup (U × Equiv.Perm Z) → Prop) (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) ≤
      ((Fintype.card Ω+Fintype.card Z).factorial : ℝ) /
        ((Fintype.card Z).factorial *
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm Ω))) : ℝ)) *
      (∑ N : {N : Subgroup U // N.Normal}, ∑ J : Subgroup (Equiv.Perm Z),
        Nat.card {β : GroupEpimorphism J (U ⧸ N.1) //
          P (fusionFullGoursatEncode N J β).1} : ℕ) := by
  have h := fusionOrbitFamily_card_le U (FusionAcceptedOrbitPredicate U P)
    (fusionOrbitNatural_and U _ P (fusionOrbitNatural_full U) hP)
  rw [fusionAcceptedOrbit_card U P] at h
  exact h

end SymmetricSubgroupAsymptotics
