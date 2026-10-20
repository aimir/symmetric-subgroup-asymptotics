import SymmetricSubgroupAsymptotics.NilpotentGeneratorQuotientLift
import SymmetricSubgroupAsymptotics.CommutingNilpotentSup
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber

/-! One actual-group step of the bounded nilpotent-core induction. An
abelian layer is split into a cheaply normally generated part and a part
centralized by the recursive source. No complement is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

theorem nilpotent_centralizer_generation_step
    {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    (A B V C : Subgroup G) [A.Normal] [B.Normal] [V.Normal] [C.Normal]
    [IsMulCommutative V] (hV : A⊔B=V) (hVC : V ≤ C)
    (hCB : C ≤ Subgroup.centralizer (B : Set G))
    (f : C →* Q) (hf : Function.Surjective f) (hker : f.ker=V.subgroupOf C)
    (JQ : Subgroup Q) [Group.IsNilpotent JQ] (SQ : Finset Q)
    (hQ : Subgroup.closure ((SQ : Set Q)∪JQ)=⊤)
    (T : Finset G) (hT : Subgroup.closure (T : Set G)⊔C=⊤)
    (t : ℕ) (hA : MarkedC4.normalGen A ≤ t) :
    ∃ (K : Subgroup G) (S : Finset G), Group.IsNilpotent K ∧
      S.card ≤ SQ.card+T.card+t ∧ Subgroup.closure ((S : Set G)∪K)=⊤ := by
  have hAV : A ≤ V := hV ▸ le_sup_left
  have hBV : B ≤ V := hV ▸ le_sup_right
  letI : IsMulCommutative A := isMulCommutative_iff.mpr (fun a b => by
    apply Subtype.ext
    exact congrArg (fun v : V => (v : G))
      (mul_comm (⟨a,hAV a.property⟩ : V) ⟨b,hAV b.property⟩))
  letI : IsMulCommutative B := isMulCommutative_iff.mpr (fun a b => by
    apply Subtype.ext
    exact congrArg (fun v : V => (v : G))
      (mul_comm (⟨a,hBV a.property⟩ : V) ⟨b,hBV b.property⟩))
  obtain ⟨J,U,hJ,hU,hlocal⟩ := lift_nilpotent_generating_set_mod_kernel f hf JQ SQ hQ
  let L : Subgroup G := J.map C.subtype
  letI : Group.IsNilpotent J := hJ
  letI : Group.IsNilpotent L := Group.nilpotent_of_mulEquiv
    (J.equivMapOfInjective C.subtype Subtype.val_injective)
  have hLC : L ≤ C := Subgroup.map_subtype_le J
  let K : Subgroup G := B⊔L
  have hK : Group.IsNilpotent K := nilpotent_sup_of_commuting B L (by
    intro b l
    exact Subgroup.mem_centralizer_iff.mp (hCB (hLC l.property)) b b.property)
  let UG : Finset G := U.image C.subtype
  let S0 : Finset G := T∪UG
  let H : Subgroup G := Subgroup.closure ((S0 : Set G)∪K)
  have hKH : K ≤ H := fun k hk => Subgroup.subset_closure (Or.inr hk)
  have hBH : B ≤ H := le_sup_left.trans hKH
  have hLH : L ≤ H := le_sup_right.trans hKH
  have hTH : Subgroup.closure (T : Set G) ≤ H := by
    apply Subgroup.closure_mono
    intro g hg
    exact Or.inl (Finset.mem_union.mpr (Or.inl hg))
  have hUH : ∀ u : C, u∈U → (u : G)∈H := by
    intro u hu
    apply Subgroup.subset_closure
    left
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨u,hu,rfl⟩))
  have hmapH : (Subgroup.closure ((U : Set C)∪J)).map C.subtype ≤ H := by
    rw [MonoidHom.map_closure]
    apply (Subgroup.closure_le H).mpr
    rintro _ ⟨u,hu,rfl⟩
    rcases hu with hu|hu
    · exact hUH u hu
    · exact hLH ⟨u,hu,rfl⟩
  have hVmap : (V.subgroupOf C).map C.subtype=V := by
    rw [Subgroup.subgroupOf_map_subtype,inf_of_le_left hVC]
  have hCeq := congrArg (fun D : Subgroup C => D.map C.subtype) hlocal
  change (Subgroup.closure ((U : Set C)∪J)⊔f.ker).map C.subtype = (⊤ : Subgroup C).map C.subtype at hCeq
  rw [Subgroup.map_sup,hker,hVmap,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hCeq
  have hCHV : C ≤ H⊔V := by
    rw [←hCeq]
    exact sup_le (hmapH.trans le_sup_left) le_sup_right
  have hHV : H⊔V=⊤ := by
    apply top_unique
    rw [←hT]
    exact sup_le (hTH.trans le_sup_left) hCHV
  have hHA : H⊔A=⊤ := by
    apply top_unique
    rw [←hHV,←hV]
    exact sup_le le_sup_left (sup_le le_sup_right (hBH.trans le_sup_left))
  obtain ⟨z,hz⟩ := exists_normal_generating_tuple_of_normalGen_le A hA
  have hzA : Set.range z ⊆ A := by rw [←hz]; exact Subgroup.subset_normalClosure
  have htop := LargeOrbitGeneratorConsequences.sup_closure_eq_top_of_abelian_normalClosure
    A z hzA hz H hHA
  let W : Finset G := Finset.univ.image z
  have hW : (W : Set G)=Set.range z := by ext g; simp only [W,Finset.coe_image,
    Finset.coe_univ,Set.image_univ]
  let S : Finset G := S0∪W
  have hS : Subgroup.closure ((S : Set G)∪K)=⊤ := by
    apply top_unique
    rw [←htop]
    apply sup_le
    · apply Subgroup.closure_mono
      intro g hg
      rcases hg with hg|hg
      · exact Or.inl (Finset.mem_union.mpr (Or.inl hg))
      · exact Or.inr hg
    · apply Subgroup.closure_mono
      intro g hg
      have hwg : g∈(W : Set G) := by rw [hW]; exact hg
      exact Or.inl (Finset.mem_union.mpr (Or.inr hwg))
  have hUG : UG.card ≤ U.card := Finset.card_image_le
  have hWcard : W.card ≤ t := by
    exact (Finset.card_image_le).trans_eq (by rw [Finset.card_univ,Fintype.card_fin])
  have hS0 : S0.card ≤ T.card+UG.card := Finset.card_union_le T UG
  have hScard : S.card ≤ S0.card+W.card := Finset.card_union_le S0 W
  exact ⟨K,S,hK,by omega,hS⟩

end SymmetricSubgroupAsymptotics
