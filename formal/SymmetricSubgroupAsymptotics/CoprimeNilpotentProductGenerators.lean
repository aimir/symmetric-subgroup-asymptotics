import SymmetricSubgroupAsymptotics.CoprimeNormalGeneratorSharing
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Nat.GCD.BigOperators

/-! Finite nilpotent factors of pairwise coprime orders reuse the same
ordinary generator positions.  This is an actual finite-product bound,
with no permutation-generator hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators

private theorem rank_le_of_surjective {G H : Type} [Group G] [Finite G] [Group H]
    (f : G→*H) (hf : Function.Surjective f) : MarkedC4.genRank H≤MarkedC4.genRank G := by
  classical
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  have hT : Subgroup.closure ((S.image f : Finset H):Set H)=⊤ := by
    have he := congrArg (Subgroup.map f) hgen
    simpa only [Finset.coe_image,MonoidHom.map_closure,
      Subgroup.map_top_of_surjective f hf] using he
  exact (MarkedC4.genRank_le hT).trans (Finset.card_image_le.trans hS.le)

theorem genRank_mulEquiv {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (e : G≃*H) : MarkedC4.genRank G=MarkedC4.genRank H :=
  le_antisymm (rank_le_of_surjective e.symm.toMonoidHom e.symm.surjective)
    (rank_le_of_surjective e.toMonoidHom e.surjective)

theorem genRank_prod_le_max (A B : Type) [Group A] [Finite A] [Group.IsNilpotent A]
    [Group B] [Finite B] [Group.IsNilpotent B]
    (hcop : (Nat.card A).Coprime (Nat.card B)) :
    MarkedC4.genRank (A×B)≤ max (MarkedC4.genRank A) (MarkedC4.genRank B) := by
  let L : Subgroup (A×B) := (MonoidHom.snd A B).ker
  let R : Subgroup (A×B) := (MonoidHom.fst A B).ker
  let eL : L≃*A :=
    { toFun := fun x=>x.val.1
      invFun := fun a=>⟨(a,1),rfl⟩
      left_inv := fun x=>Subtype.ext (Prod.ext rfl x.property.symm)
      right_inv := fun _=>rfl
      map_mul' := fun _ _=>rfl }
  let eR : R≃*B :=
    { toFun := fun x=>x.val.2
      invFun := fun b=>⟨(1,b),rfl⟩
      left_inv := fun x=>Subtype.ext (Prod.ext x.property.symm rfl)
      right_inv := fun _=>rfl
      map_mul' := fun _ _=>rfl }
  have hjoin : L⊔R=⊤ := by
    apply top_unique
    rintro ⟨a,b⟩ _
    have hl : (a,1)∈L⊔R := (le_sup_left : L≤L⊔R) (show (a,1)∈L from rfl)
    have hr : (1,b)∈L⊔R := (le_sup_right : R≤L⊔R) (show (1,b)∈R from rfl)
    simpa only [Prod.mk_mul_mk,mul_one,one_mul] using (L⊔R).mul_mem hl hr
  have hcop' : (Nat.card L).Coprime (Nat.card R) := by
    simpa only [Nat.card_congr eL.toEquiv,Nat.card_congr eR.toEquiv] using hcop
  have h := CoprimeNormalGeneratorSharing.nilpotent_genRank_le_max_of_normal_join L R hjoin hcop'
  simpa only [genRank_mulEquiv eL,genRank_mulEquiv eR] using h

private def optionPiEquiv {ι : Type} (M : Option ι→Type) [∀i,Group (M i)] :
    (∀i,M i)≃*M none × (∀i,M (some i)) :=
  { Equiv.piOptionEquivProd with map_mul' := fun _ _=>rfl }

/-- A finite family of coprime nilpotent factors costs their largest
ordinary generating rank, expressed without choosing a maximizing index. -/
theorem genRank_pi_le {ι : Type} [Finite ι] (M : ι→Type)
    [∀i,Group (M i)] [∀i,Finite (M i)] [∀i,Group.IsNilpotent (M i)]
    (hcop : Pairwise (fun i j=>(Nat.card (M i)).Coprime (Nat.card (M j))))
    (d : ℕ) (hrank : ∀i,MarkedC4.genRank (M i)≤d) :
    MarkedC4.genRank (∀i,M i)≤d := by
  classical
  let P : Type→Prop := fun I=>∀[Finite I] (N:I→Type) [∀i,Group (N i)] [∀i,Finite (N i)]
    [∀i,Group.IsNilpotent (N i)],
    Pairwise (fun i j=>(Nat.card (N i)).Coprime (Nat.card (N j)))→
    (∀i,MarkedC4.genRank (N i)≤d)→MarkedC4.genRank (∀i,N i)≤d
  have h : P ι := by
    intro _
    apply Finite.induction_empty_option (P:=P) ?_ ?_ ?_ ι
    · intro I J e hI _ N _ _ _ hc hd
      letI : Finite I := Finite.of_equiv J e.symm
      let E : (∀j,N j)≃*(∀i,N (e i)) :=
        { (Equiv.piCongrLeft N e).symm with map_mul' := fun _ _=>rfl }
      rw [genRank_mulEquiv E]
      exact hI (fun i=>N (e i)) (fun i j hij=>hc (by exact fun he=>hij (e.injective he)))
        (fun i=>hd (e i))
    · intro _ N _ _ _ _ _
      have hg : Subgroup.closure (∅:Set (∀i:PEmpty,N i))=⊤ := by
        apply top_unique
        intro x _
        have hx : x=1 := Subsingleton.elim _ _
        rw [hx]
        exact Subgroup.one_mem _
      exact (MarkedC4.genRank_le (s:=∅) (by simpa only [Finset.coe_empty] using hg)).trans (Nat.zero_le d)
    · intro I _ hI _ N _ _ _ hc hd
      have htail : MarkedC4.genRank (∀i,N (some i))≤d :=
        hI (fun i=>N (some i)) (fun i j hij=>hc (by simpa using hij)) (fun i=>hd (some i))
      have hhead : (Nat.card (N none)).Coprime (Nat.card (∀i,N (some i))) := by
        rw [Nat.card_pi]
        exact Nat.coprime_fintype_prod_right_iff.mpr (fun i=>hc (by simp))
      rw [genRank_mulEquiv (optionPiEquiv N)]
      exact (genRank_prod_le_max (N none) (∀i,N (some i)) hhead).trans
        (max_le (hd none) htail)
  exact h M hcop hrank

end SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
