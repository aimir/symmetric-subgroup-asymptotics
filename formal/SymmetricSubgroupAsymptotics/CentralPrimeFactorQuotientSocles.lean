import SymmetricSubgroupAsymptotics.CentralFactorNormalAxes
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! A central prime factor shares a socle generator with a nontrivial
minimal self-centralizing core. Every original quotient either kills the
core, kills exactly the central factor, or has trivial kernel. The two
actual projections retain the respective quotient maps. -/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace CentralBinaryProductCore

variable {L : Type} [Group L] (D : CentralBinaryProductCore L)
variable (C : Type) [CommGroup C] [IsSimpleGroup C]

theorem productCore_ne_bot (hV : D.V ≠ ⊥) : D.productCore C ≠ ⊥ := by
  obtain ⟨v,hv,hvne⟩ := D.V.bot_or_exists_ne_one.resolve_left hV
  intro h
  have hm : (v,(1 : C)) ∈ D.productCore C := (D.mem_productCore C _).mpr ⟨hv,rfl⟩
  rw [h] at hm
  exact hvne (congrArg Prod.fst (Subgroup.mem_bot.mp hm))

theorem productCentral_minimal
    (W : Subgroup (L × C)) (hW : W.Normal) (hWC : W ≤ D.productCentral C) :
    W = ⊥ ∨ W = D.productCentral C := by
  let pi : L × C →* C := MonoidHom.snd L C
  have hnormal : (W.map pi).Normal := hW.map pi Prod.snd_surjective
  rcases hnormal.eq_bot_or_eq_top with hb | ht
  · left
    apply le_antisymm _ bot_le
    intro w hw
    apply Subgroup.mem_bot.mpr
    apply Prod.ext
    · exact (D.mem_productCentral C w).mp (hWC hw)
    · apply Subgroup.mem_bot.mp
      rw [← hb]
      exact ⟨w,hw,rfl⟩
  · right
    apply le_antisymm hWC
    intro c hc
    have hm : c.2 ∈ W.map pi := by rw [ht]; exact Subgroup.mem_top _
    obtain ⟨w,hw,he⟩ := hm
    have heq : w = c := Prod.ext
      (((D.mem_productCentral C w).mp (hWC hw)).trans
        ((D.mem_productCentral C c).mp hc).symm) he
    rwa [← heq]

theorem productCentral_ne_bot : D.productCentral C ≠ ⊥ := by
  obtain ⟨c,hc⟩ := exists_ne (1 : C)
  intro h
  have hm : ((1 : L),c) ∈ D.productCentral C := (D.mem_productCentral C _).mpr rfl
  rw [h] at hm
  exact hc (congrArg Prod.snd (Subgroup.mem_bot.mp hm))

theorem productCore_isMinimalNormal (hV : D.V ≠ ⊥) :
    IsMinimalNormalSubgroup (D.productCore C) :=
  ⟨inferInstance,D.productCore_ne_bot C hV,fun W hW hWne hWC =>
    (D.productCore_minimal C W hW hWC).resolve_left hWne⟩

theorem productCentral_isMinimalNormal :
    IsMinimalNormalSubgroup (D.productCentral C) :=
  ⟨inferInstance,D.productCentral_ne_bot C,fun W hW hWne hWC =>
    (D.productCentral_minimal C W hW hWC).resolve_left hWne⟩

theorem product_socle (hV : D.V ≠ ⊥) :
    finiteGroupSocle (L × C) = D.productCore C ⊔ D.productCentral C := by
  have hA := D.productCore_isMinimalNormal C hV
  have hB := D.productCentral_isMinimalNormal C
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x ⟨N,hN,hx⟩
    rcases D.normal_contains_productCore_or_le_productCentral C N hN.1 with ha | hb
    · have he : D.productCore C = N := hN.2.2 _ inferInstance hA.2.1 ha
      exact Subgroup.mem_sup_left (he.symm ▸ hx)
    · exact Subgroup.mem_sup_right (hb hx)
  · apply sup_le
    · intro x hx
      exact Subgroup.subset_normalClosure ⟨_,hA,hx⟩
    · intro x hx
      exact Subgroup.subset_normalClosure ⟨_,hB,hx⟩

theorem productCore_commutator_full (hV : D.V ≠ ⊥) :
    ⁅(⊤ : Subgroup (L × C)),D.productCore C⁆ = D.productCore C := by
  rcases D.productCore_minimal C ⁅(⊤ : Subgroup (L × C)),D.productCore C⁆
      inferInstance (Subgroup.commutator_le_right _ _) with hb | ht
  · exfalso
    apply hV
    apply le_antisymm _ bot_le
    intro v hv
    apply Subgroup.mem_bot.mpr
    apply D.noFixed v hv
    intro x
    have hm : ⁅(x,(1 : C)),(v,(1 : C))⁆ ∈
        ⁅(⊤ : Subgroup (L × C)),D.productCore C⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
        ((D.mem_productCore C _).mpr ⟨hv,rfl⟩)
    rw [hb] at hm
    have he := congrArg Prod.fst (Subgroup.mem_bot.mp hm)
    change x*v*x⁻¹*v⁻¹ = 1 at he
    calc
      x*v = (x*v*x⁻¹*v⁻¹)*(v*x) := by group
      _ = v*x := by rw [he,one_mul]
  · exact ht

private theorem normalGen_le_one_of_minimal
    {G : Type} [Group G] (M : Subgroup G) (hM : IsMinimalNormalSubgroup M) :
    MarkedC4.normalGen M ≤ 1 := by
  letI := hM.1
  obtain ⟨x,hx,hxne⟩ := M.bot_or_exists_ne_one.resolve_left hM.2.1
  let T := Subgroup.normalClosure (Set.range (fun _ : Fin 1 => x))
  have hTM : T ≤ M := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i,rfl⟩
    exact hx
  have hTne : T ≠ ⊥ := by
    intro h
    apply hxne
    have hm : x ∈ T := Subgroup.subset_normalClosure (Set.mem_range_self (0 : Fin 1))
    rw [h] at hm
    exact Subgroup.mem_bot.mp hm
  exact normalGen_le_of_fin_tuple (fun _ : Fin 1 => x)
    (hM.2.2 T inferInstance hTne hTM)

theorem product_socle_one [Finite L] [Finite C] (hV : D.V ≠ ⊥) :
    SocleNormalGeneratorBound (L × C) 1 := by
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).mpr
  rw [D.product_socle C hV]
  have hNC : NoCommonNormalQuotient (D.productCore C) (D.productCentral C) := by
    apply noCommonNormalQuotient_of_commutator_full_central (⊤ : Subgroup (L × C))
    · exact D.productCore_commutator_full C hV
    · intro z hz
      apply Subgroup.mem_centralizer_iff.mpr
      intro x _
      apply Prod.ext
      · change x.1*z.1 = z.1*x.1
        rw [(D.mem_productCentral C z).mp hz]
        simp
      · exact mul_comm _ _
  exact (normalGen_sup_le_max_of_noCommonNormalQuotient _ _ hNC).trans
    (max_le (normalGen_le_one_of_minimal _ (D.productCore_isMinimalNormal C hV))
      (normalGen_le_one_of_minimal _ (D.productCentral_isMinimalNormal C)))

/-- Transfer across the actual core and the actual central axis. Both
smaller all-quotient bounds are hypotheses on displayed groups, never on
newly chosen isomorphic replacements of an original quotient. -/
theorem product_socle_of_surjective [Finite L] [Finite C]
    (hV : D.V ≠ ⊥) {Q : Type} [Group Q]
    (pi : L →* Q) (hpi : Function.Surjective pi) (hker : pi.ker = D.V)
    {t : ℕ} (ht : 1 ≤ t)
    (hL : ∀ N : Subgroup L, ∀ _ : N.Normal, SocleNormalGeneratorBound (L ⧸ N) t)
    (hQ : ∀ N : Subgroup (Q × C), ∀ _ : N.Normal,
      SocleNormalGeneratorBound ((Q × C) ⧸ N) t)
    {X : Type} [Group X] (rho : L × C →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X t := by
  let P : L × C →* Q × C := pi.prodMap (MonoidHom.id C)
  have hP : Function.Surjective P := by
    intro q
    obtain ⟨l,hl⟩ := hpi q.1
    exact ⟨(l,q.2),Prod.ext hl rfl⟩
  have hPk : P.ker = D.productCore C := by
    ext x
    change (pi x.1,x.2) = 1 ↔ x.1 ∈ D.V ∧ x.2 = 1
    rw [← hker,MonoidHom.mem_ker]
    exact Prod.ext_iff
  rcases D.normal_contains_productCore_or_le_productCentral C rho.ker inferInstance with hk | hc
  · have hPkilled : P.ker ≤ rho.ker := by rw [hPk]; exact hk
    obtain ⟨f,hf,_⟩ := CyclicSocleQuotientTools.exists_surjective_factor P hP rho hrho hPkilled
    exact CyclicSocleQuotientTools.socleBound_equiv
      (QuotientGroup.quotientKerEquivOfSurjective f hf) (hQ f.ker inferInstance)
  · rcases D.productCentral_minimal C rho.ker inferInstance hc with hb | he
    · exact CyclicSocleQuotientTools.socleBound_equiv
        (MulEquiv.ofBijective rho ⟨(MonoidHom.ker_eq_bot_iff rho).mp hb,hrho⟩)
        ((D.product_socle_one C hV).mono ht)
    · have hfst : (MonoidHom.fst L C).ker ≤ rho.ker := by
        intro x hx
        rw [he]
        exact (D.mem_productCentral C x).mpr (MonoidHom.mem_ker.mp hx)
      obtain ⟨f,hf,_⟩ := CyclicSocleQuotientTools.exists_surjective_factor
        (MonoidHom.fst L C) Prod.fst_surjective rho hrho hfst
      exact CyclicSocleQuotientTools.socleBound_equiv
        (QuotientGroup.quotientKerEquivOfSurjective f hf) (hL f.ker inferInstance)

end CentralBinaryProductCore
end SymmetricSubgroupAsymptotics

end
