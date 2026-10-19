import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkedRDTSource

/-! Exact rank, normal-budget and epimorphism transport between the SAME
marked subgroup and its literal bounded-factor RDT source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedRDTTransport
open ActualMarkedRDTSource ActualGlobalMarkGeneratorRank ActualMarkZeroNormalRank

variable {s u : ℕ} (R : Fin s → Type) [∀ i,Group (R i)] [∀ i,Finite (R i)]
  (P : Fin u → Type) [∀ j,Group (P j)] [∀ j,Finite (P j)]
  (r : ℕ) (A : Subgroup (((∀ i,R i) × (∀ j,P j)) × Marks r))

def sourceTail : Source R P r A →* (∀ j,P j) :=
  (MonoidHom.snd (Left R P r A) (∀ j,P j)).comp (Source R P r A).subtype

theorem tail_inverse_comp : (tail R P r A).comp
    (sourceEquiv R P r A).symm.toMonoidHom=sourceTail R P r A := by
  apply MonoidHom.ext
  intro x
  obtain ⟨a,rfl⟩ := (sourceEquiv R P r A).surjective x
  change tail R P r A ((sourceEquiv R P r A).symm (sourceEquiv R P r A a))=
    sourceTail R P r A (sourceEquiv R P r A a)
  rw [(sourceEquiv R P r A).symm_apply_apply]
  rfl

theorem genRank_eq : genRank (Source R P r A)=genRank A := by
  apply le_antisymm
  · exact genRank_le_of_surjective (sourceEquiv R P r A).toMonoidHom
      (sourceEquiv R P r A).surjective
  · exact genRank_le_of_surjective (sourceEquiv R P r A).symm.toMonoidHom
      (sourceEquiv R P r A).symm.surjective

theorem normal_budget (dN : ℕ)
    (hA : ∀ V : Subgroup A,V.Normal →V≤commutator A ⊓ (tail R P r A).ker →normalGen V≤dN) :
    ∀ U : Subgroup (Source R P r A),U.Normal →
      U≤commutator (Source R P r A) ⊓ (sourceTail R P r A).ker →normalGen U≤dN := by
  intro U hUn hU
  letI : U.Normal := hUn
  let q := (sourceEquiv R P r A).symm.toMonoidHom
  have hq : Function.Surjective q := (sourceEquiv R P r A).symm.surjective
  letI : (U.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hd : (commutator (Source R P r A)).map q=commutator A := by
    rw [map_commutator_eq,q.range_eq_top_of_surjective hq]
    rfl
  have hV : U.map q≤commutator A ⊓ (tail R P r A).ker := by
    rintro a ⟨x,hx,rfl⟩
    constructor
    · rw [← hd]
      exact ⟨x,(hU hx).1,rfl⟩
    · have ht := (hU hx).2
      change sourceTail R P r A x=1 at ht
      change (tail R P r A).comp q x=1
      rw [tail_inverse_comp]
      exact ht
  have he : normalGen (U.map q)=normalGen U := by
    apply normalGen_map_eq q hq U
    intro x hx he
    apply (sourceEquiv R P r A).symm.injective
    exact he.trans q.map_one.symm
  rw [← he]
  exact hA _ inferInstance hV

def epiEquiv (Q : Type) [Group Q] :
    {f : A →* Q // Function.Surjective f} ≃
      {f : Source R P r A →* Q // Function.Surjective f} where
  toFun f := ⟨f.val.comp (sourceEquiv R P r A).symm.toMonoidHom,
    f.property.comp (sourceEquiv R P r A).symm.surjective⟩
  invFun f := ⟨f.val.comp (sourceEquiv R P r A).toMonoidHom,
    f.property.comp (sourceEquiv R P r A).surjective⟩
  left_inv f := by apply Subtype.ext; ext x; simp
  right_inv f := by apply Subtype.ext; ext x; simp

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedRDTTransport
