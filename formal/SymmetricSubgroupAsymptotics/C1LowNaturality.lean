import SymmetricSubgroupAsymptotics.C1LowNormalized
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters
import SymmetricSubgroupAsymptotics.FusionPhysicalCount

/-! Restricting a physical c=1 family to the low cone is automatically
natural. Only the original survival predicate needs structural invariance;
no extra conjugacy or numerical premise is imposed on its low part. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem ternaryCharacterRank_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    ternaryCharacterRank G=ternaryCharacterRank H := primeCharacter_finrank_congr 3 e

theorem ternaryCharacterRank_map_conj {G : Type*} [Group G] (K : Subgroup G) (g : G) :
    ternaryCharacterRank (K.map (MulAut.conj g).toMonoidHom)=ternaryCharacterRank K :=
  (ternaryCharacterRank_congr (K.equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).symm

theorem ternaryPhysicalPredicate_iff {Z : Type*}
    (P : Subgroup (TernaryCyclic×Equiv.Perm Z) → Prop)
    (H : Subgroup (ternaryRegularAction×Equiv.Perm Z)) :
    TernaryPhysicalPredicate P H ↔ ∃ d : TernaryGraphData (Equiv.Perm Z),
      TernarySplit d.2 ∧ P (ternaryActualGraph d) ∧
        (ternaryActualGraph d).map ternaryPhysicalCoordinateEquiv.toMonoidHom=H := by
  constructor
  · rintro ⟨h,he⟩
    obtain ⟨d,hd⟩ := h.2
    refine ⟨d.1,d.2.1,d.2.2,?_⟩
    dsimp only at hd
    rw [hd]
    exact he
  · rintro ⟨d,hs,hp,he⟩
    exact ⟨⟨ternaryActualGraph d,⟨⟨d,hs,hp⟩,rfl⟩⟩,he⟩

theorem ternaryPhysicalGraph_complement {Z : Type*} (d : TernaryGraphData (Equiv.Perm Z)) :
    ((ternaryActualGraph d).map ternaryPhysicalCoordinateEquiv.toMonoidHom).map
      (MonoidHom.snd ternaryRegularAction (Equiv.Perm Z))=d.1 := by
  rw [Subgroup.map_map]
  change (ternaryActualGraph d).map (MonoidHom.snd TernaryCyclic (Equiv.Perm Z))=d.1
  exact ternaryActualGraph_complement d

theorem ternaryPhysicalPredicate_low_iff (m : ℕ)
    (P : Subgroup (TernaryCyclic×Equiv.Perm (Fin m)) → Prop)
    (H : Subgroup (ternaryRegularAction×Equiv.Perm (Fin m))) :
    TernaryPhysicalPredicate (C1LowGraphPredicate m P) H ↔
      TernaryPhysicalPredicate P H ∧ 20*ternaryCharacterRank
        (H.map (MonoidHom.snd ternaryRegularAction (Equiv.Perm (Fin m))))≤3*m := by
  rw [ternaryPhysicalPredicate_iff,ternaryPhysicalPredicate_iff]
  constructor
  · rintro ⟨⟨K,χ⟩,hs,hp,rfl⟩
    have hp' := (c1LowGraphPredicate_actualGraph m P K χ).mp hp
    refine ⟨⟨⟨K,χ⟩,hs,hp'.1,rfl⟩,?_⟩
    have hr := congrArg (fun L : Subgroup (Equiv.Perm (Fin m)) => ternaryCharacterRank L)
      (ternaryPhysicalGraph_complement (Z := Fin m) ⟨K,χ⟩)
    simpa only [hr] using hp'.2
  · rintro ⟨⟨⟨K,χ⟩,hs,hp,rfl⟩,hr⟩
    refine ⟨⟨K,χ⟩,hs,?_,rfl⟩
    apply (c1LowGraphPredicate_actualGraph m P K χ).mpr
    refine ⟨hp,?_⟩
    have he := congrArg (fun L : Subgroup (Equiv.Perm (Fin m)) => ternaryCharacterRank L)
      (ternaryPhysicalGraph_complement (Z := Fin m) ⟨K,χ⟩)
    simpa only [he] using hr

theorem ternaryPhysicalPredicate_low_natural (m : ℕ)
    (P : Subgroup (TernaryCyclic×Equiv.Perm (Fin m)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction (TernaryPhysicalPredicate P)) :
    FusionOrbitNatural ternaryRegularAction (TernaryPhysicalPredicate (C1LowGraphPredicate m P)) := by
  have hsource := fusionOrbitNatural_source (Z := Fin m) ternaryRegularAction
    (fun K => 20*ternaryCharacterRank K≤3*m) (by
      intro c K hk
      simpa only [ternaryCharacterRank_map_conj] using hk)
  have h := fusionOrbitNatural_and ternaryRegularAction _ _ hP hsource
  intro c H hH
  exact (ternaryPhysicalPredicate_low_iff m P _).mpr
    (h c H ((ternaryPhysicalPredicate_low_iff m P H).mp hH))

/-- The low-cone numerical row is installed for every original natural
surviving family, without a separate low-cone invariance assumption. -/
theorem c1Low_physical_normalized_of_natural (m : ℕ)
    (P : Subgroup (TernaryCyclic×Equiv.Perm (Fin m)) → Prop)
    (hP : FusionOrbitNatural ternaryRegularAction (TernaryPhysicalPredicate P)) :
    (Nat.card (FusionOrbitFamily ternaryRegularAction
      (TernaryPhysicalPredicate (C1LowGraphPredicate m P))):ℝ)/exactBenchmark (m+3) ≤
        c1LowKernel m*((subgroupCount m:ℝ)/exactBenchmark m) :=
  c1Low_physical_normalized m P (ternaryPhysicalPredicate_low_natural m P hP)

end SymmetricSubgroupAsymptotics
