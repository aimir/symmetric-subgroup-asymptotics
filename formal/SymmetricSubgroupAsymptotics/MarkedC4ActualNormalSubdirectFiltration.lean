import SymmetricSubgroupAsymptotics.MarkedC4ActualSubdirectFiltration

/-! Actual filtration of a NORMAL subgroup in a literal subdirect source.
All diagonal normal ranks are in the actual physical quotient factors. This
allows ordinary local rank results to descend from original transitive
factors without assigning invented transitive actions to their quotients. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalSubdirectFiltration
open ActualSubdirectFiltration

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (G : Subgroup (∀ i,F i)) (U : Subgroup G) [U.Normal]
  (hsurj : ∀ i,Function.Surjective (coordinate F G i))

def layer (m : ℕ) : Subgroup G := U ⊓ «prefix» F G m
instance layerNormal (m : ℕ) : (layer F G U m).Normal := inferInstanceAs (U ⊓ «prefix» F G m).Normal
def diagonal (i : Fin t) : Subgroup (F i) :=
  (layer F G U (i.val+1)).map (coordinate F G i)

instance diagonalNormal (i : Fin t) : (diagonal F G U i).Normal :=
  Subgroup.Normal.map inferInstance (coordinate F G i) (hsurj i)

theorem layer_zero : layer F G U 0=⊥ := by simp [layer,prefix_zero]
theorem layer_full : layer F G U t=U := by simp [layer,prefix_full]
theorem layer_kernel (i : Fin t) (x : G) (hx : x∈layer F G U (i.val+1))
    (he : coordinate F G i x=1) : x∈layer F G U i.val :=
  ⟨hx.1,prefix_kernel F G i x hx.2 he⟩

include hsurj in
theorem exists_generators (i : Fin t) :
    ∃ S : Finset G,S.card≤normalGen (diagonal F G U i) ∧
      (S : Set G)⊆layer F G U (i.val+1) ∧
      layer F G U (i.val+1)≤Subgroup.normalClosure (S : Set G) ⊔ layer F G U i.val := by
  letI : (diagonal F G U i).Normal := diagonalNormal F G U hsurj i
  obtain ⟨s,hcard,hs,hgen⟩ := normalGen_spec (diagonal F G U i)
  obtain ⟨S,hS,hmem,hstep⟩ := exists_layer_lift (coordinate F G i) (hsurj i)
    (layer F G U i.val) (layer F G U (i.val+1)) (layer_kernel F G U i) s hs hgen
  exact ⟨S,hS.trans_eq hcard,hmem,hstep⟩

def generators (m : ℕ) : Finset G :=
  if hm : m<t then Classical.choose (exists_generators F G U hsurj ⟨m,hm⟩) else ∅

theorem generators_spec (m : ℕ) (hm : m<t) :
    (generators F G U hsurj m).card≤normalGen (diagonal F G U ⟨m,hm⟩) ∧
      (generators F G U hsurj m : Set G)⊆layer F G U (m+1) ∧
      layer F G U (m+1)≤Subgroup.normalClosure (generators F G U hsurj m : Set G) ⊔
        layer F G U m := by
  simpa only [generators,dif_pos hm] using
    Classical.choose_spec (exists_generators F G U hsurj ⟨m,hm⟩)

include hsurj in
theorem normalGen_le_sum_diagonal : normalGen U≤∑ i : Fin t,normalGen (diagonal F G U i) := by
  have h := normalGen_le_sum_of_chain U t (layer F G U) (layer_zero F G U)
    (layer_full F G U) (generators F G U hsurj)
    (fun m hm => (generators_spec F G U hsurj m hm).2.1)
    (fun m hm => (generators_spec F G U hsurj m hm).2.2)
    (fun m _ => inf_le_left)
  apply h.trans
  rw [show (∑ i : Fin t,normalGen (diagonal F G U i))=
      ∑ m ∈ Finset.range t,if hm : m<t then normalGen (diagonal F G U ⟨m,hm⟩) else 0 from by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i hi; exact Finset.mem_range.mpr i.isLt
    · intro i hi j hj he; exact Fin.ext he
    · intro m hm; exact ⟨⟨m,Finset.mem_range.mp hm⟩,Finset.mem_univ _,rfl⟩
    · intro i hi; simp only [dif_pos i.isLt]]
  apply Finset.sum_le_sum
  intro m hm
  simpa only [dif_pos (Finset.mem_range.mp hm)] using
    (generators_spec F G U hsurj m (Finset.mem_range.mp hm)).1

include hsurj in
/-- Relevant derived normal subgroups have actual derived diagonal images. -/
theorem diagonal_le_derived (hU : U≤commutator G) (i : Fin t) :
    diagonal F G U i≤commutator (F i) := by
  have he : (commutator G).map (coordinate F G i)=commutator (F i) := by
    rw [map_commutator_eq,(coordinate F G i).range_eq_top_of_surjective (hsurj i)]
    rfl
  rw [← he]
  exact Subgroup.map_mono (inf_le_left.trans hU)

theorem diagonal_eq_bot_of_zero (i : Fin t)
    (hzero : ∀ x∈U,coordinate F G i x=1) : diagonal F G U i=⊥ := by
  apply le_antisymm _ bot_le
  rintro q ⟨x,hx,rfl⟩
  exact Subgroup.mem_bot.mpr (hzero x hx.1)

include hsurj in
/-- Actual dependent-normal budget from ordinary local derived-normal
bounds. Independent-tail diagonals vanish; no quotient action is invented. -/
theorem derived_tail_rank_le (tail : Finset (Fin t)) (weight : Fin t → ℝ)
    (hU : U≤commutator G)
    (hzero : ∀ i∈tail,∀ x∈U,coordinate F G i x=1)
    (hlocal : ∀ (i : Fin t) (V : Subgroup (F i)),V.Normal →V≤commutator (F i) →
      (normalGen V : ℝ)≤weight i/4) :
    (normalGen U : ℝ)≤∑ i : Fin t,if i∈tail then 0 else weight i/4 := by
  have hbase : (normalGen U : ℝ)≤∑ i : Fin t,(normalGen (diagonal F G U i) : ℝ) := by
    exact_mod_cast normalGen_le_sum_diagonal F G U hsurj
  apply hbase.trans
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i∈tail
  · rw [if_pos hi,diagonal_eq_bot_of_zero F G U i (hzero i hi),normalGen_bot]
    norm_num
  · rw [if_neg hi]
    exact hlocal i _ (diagonalNormal F G U hsurj i) (diagonal_le_derived F G U hsurj hU i)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalSubdirectFiltration
