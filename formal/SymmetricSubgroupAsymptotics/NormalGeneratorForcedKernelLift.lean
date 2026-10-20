import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineSocleGenerators

/-! A kernel forced by the lifted normal generators costs no extra slot.
The force condition is structural and concerns actual normal subgroups;
there is no splitting hypothesis on the original quotient. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

 theorem normalGen_le_forcedKernelLift
    {G : Type} [Group G] [Finite G]
    (D N : Subgroup G) [D.Normal] [N.Normal]
    (hforce : ∀ C : Subgroup G, C.Normal → N ≤ C ⊔ D → D ≤ C) :
    MarkedC4.normalGen N ≤
      MarkedC4.normalGen (N.map (QuotientGroup.mk' D)) := by
  let q := QuotientGroup.mk' D
  letI : (N.map q).Normal := (inferInstance : N.Normal).map q
    (QuotientGroup.mk'_surjective D)
  obtain ⟨b,hbCard,hbSub,hbClosure⟩ := MarkedC4.normalGen_spec (N.map q)
  obtain ⟨c,hcCard,hcSub,hcStep⟩ := MarkedC4.exists_layer_lift q
    (QuotientGroup.mk'_surjective D) D N
    (fun x _ hx => (QuotientGroup.eq_one_iff x).mp hx) b hbSub hbClosure
  have hD : D ≤ Subgroup.normalClosure (c : Set G) :=
    hforce _ inferInstance hcStep
  have hclosure : Subgroup.normalClosure (c : Set G) = N :=
    le_antisymm (Subgroup.normalClosure_le_normal hcSub)
      (hcStep.trans (sup_le le_rfl hD))
  simpa only [q] using (MarkedC4.normalGen_le hcSub hclosure).trans
    (hcCard.trans hbCard.le)

/-- Small actual normal subgroups have short ambient normal tuples. -/
theorem normalGen_le_of_card_le_eight
    {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hcard : Nat.card N ≤ 8) : MarkedC4.normalGen N ≤ 3 := by
  obtain ⟨S,hS,hsize⟩ := MarkedC4.exists_generating_finset_card_le N
  have hthree : S.card ≤ 3 := by
    have hpow : 2^S.card ≤ 2^3 := hsize.trans hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hpow
  let T := S.image N.subtype
  have hTS : (T : Set G) ⊆ N := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have hcl : Subgroup.closure (T : Set G) = N := by
    have h := N.subtype.map_closure (S : Set N)
    have htop : (⊤ : Subgroup N).map N.subtype=N := by
      ext x
      constructor
      · rintro ⟨y,_,rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x,hx⟩,Subgroup.mem_top _,rfl⟩
    rw [hS,htop] at h
    simpa only [T,Finset.coe_image] using h.symm
  have hncl : Subgroup.normalClosure (T : Set G) = N :=
    le_antisymm (Subgroup.normalClosure_le_normal hTS)
      (hcl ▸ Subgroup.closure_le_normalClosure)
  exact (MarkedC4.normalGen_le hTS hncl).trans
    (Finset.card_image_le.trans hthree)

end SymmetricSubgroupAsymptotics
end
