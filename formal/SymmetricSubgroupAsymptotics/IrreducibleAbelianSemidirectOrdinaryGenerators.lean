import SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectNormalGenerators
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! Ordinary generation in an actual irreducible abelian semidirect
product. One nonidentity translation, together with ordinary generators
of the complement, generates the entire original semidirect product.
No faithful action or normal-generation surrogate is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectOrdinaryGenerators
open SemidirectProduct

variable {V H : Type} [CommGroup V] [Group H] (φ : H→*MulAut V)

theorem closure_insert_translation (hirr : IrreducibleAbelianSemidirect.Irreducible φ)
    (s : Finset H) (hs : Subgroup.closure (s:Set H)=⊤) (v : V) (hv : v≠1) :
    Subgroup.closure
      ((insert (inl v) (s.image (inr : H→*V⋊[φ]H)) : Finset (V⋊[φ]H)):Set (V⋊[φ]H))=⊤ := by
  classical
  let K : Subgroup (V⋊[φ]H) := Subgroup.closure
    ((insert (inl v) (s.image (inr : H→*V⋊[φ]H)) : Finset (V⋊[φ]H)):Set (V⋊[φ]H))
  have hH : ∀h:H,(inr h : V⋊[φ]H)∈K := by
    have hh : Subgroup.closure (s:Set H)≤K.comap (inr : H→*V⋊[φ]H) := by
      apply (Subgroup.closure_le (K.comap (inr : H→*V⋊[φ]H))).mpr
      intro h hh
      apply Subgroup.subset_closure
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨h,hh,rfl⟩)
    rw [hs] at hh
    exact fun h=>hh (Subgroup.mem_top h)
  let S : Subgroup V := K.comap (inl : V→*V⋊[φ]H)
  have hSinv : ∀h w,w∈S→φ h w∈S := by
    intro h w hw
    change (inl (φ h w) : V⋊[φ]H)∈K
    rw [inl_aut]
    simpa only [map_inv] using K.mul_mem (K.mul_mem (hH h) hw) (K.inv_mem (hH h))
  have hvS : v∈S := Subgroup.subset_closure (Finset.mem_insert_self _ _)
  have hSne : S≠⊥ := by
    intro hb
    exact hv (Subgroup.mem_bot.mp (hb ▸ hvS))
  have hStop : S=⊤ := (hirr S hSinv).resolve_left hSne
  apply top_unique
  intro g _
  have hleft : (inl g.left : V⋊[φ]H)∈K := by
    have hh : g.left∈S := by rw [hStop]; exact Subgroup.mem_top _
    exact hh
  rw [←inl_left_mul_inr_right g]
  exact K.mul_mem hleft (hH g.right)

theorem exists_generating_finset [Finite H] [Nontrivial V]
    (hirr : IrreducibleAbelianSemidirect.Irreducible φ) :
    ∃S:Finset (V⋊[φ]H),Subgroup.closure (S:Set (V⋊[φ]H))=⊤ ∧
      S.card≤MarkedC4.genRank H+1 := by
  classical
  obtain ⟨s,hs,hgen⟩ := MarkedC4.genRank_spec (G:=H)
  obtain ⟨v,hv⟩ := exists_ne (1:V)
  refine ⟨insert (inl v) (s.image (inr : H→*V⋊[φ]H)),
    closure_insert_translation φ hirr s hgen v hv,?_⟩
  exact (Finset.card_insert_le _ _).trans
    ((Nat.add_le_add_right Finset.card_image_le 1).trans_eq (congrArg (fun n=>n+1) hs))

theorem genRank_le_complement_add_one [Finite H] [Nontrivial V]
    (hirr : IrreducibleAbelianSemidirect.Irreducible φ) :
    MarkedC4.genRank (V⋊[φ]H)≤MarkedC4.genRank H+1 := by
  obtain ⟨S,hgen,hcard⟩ := exists_generating_finset φ hirr
  exact (MarkedC4.genRank_le hgen).trans hcard

end SymmetricSubgroupAsymptotics.IrreducibleAbelianSemidirectOrdinaryGenerators
