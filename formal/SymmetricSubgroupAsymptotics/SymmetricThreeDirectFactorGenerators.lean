import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.Tactic.Group

/-! Ordinary generator sharing with a literal S3 direct factor. One
3-cycle is paired with an existing complement generator. A single pure
transposition then extracts that 3-cycle by a commutator. This retains
one shared generator slot even when the factors have common quotients. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SymmetricThreeDirectFactorGenerators

private abbrev S3 := Equiv.Perm (Fin 3)
private def a : S3 := Equiv.swap 1 2
private def b : S3 := finRotate 3

private theorem generated : Subgroup.closure ({b,a}:Set S3)=⊤ := by
  simpa only [a,b,show finRotate 3 (1:Fin 3)=2 from rfl] using
    Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate_of_le (by decide : 2≤3))
      (support_finRotate_of_le (by decide : 2≤3)) (1:Fin 3)

private theorem commutator_extract : a*b*a⁻¹*b⁻¹=b := by decide +kernel

private theorem share_nonempty {Q : Type} [Group Q]
    (s : Finset Q) (hgen : Subgroup.closure (s:Set Q)=⊤) (q₀ : Q) (hq₀ : q₀∈s) :
    ∃T:Finset (S3×Q),Subgroup.closure (T:Set (S3×Q))=⊤ ∧ T.card≤s.card+1 := by
  let T : Finset (S3×Q) := insert (a,1) (insert (b,q₀)
    ((s.erase q₀).image (fun q:Q=>((1:S3),q))))
  let K := Subgroup.closure (T:Set (S3×Q))
  have hA : (a,1)∈K := Subgroup.subset_closure (Finset.mem_insert_self _ _)
  have hBq : (b,q₀)∈K := Subgroup.subset_closure
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hB : (b,1)∈K := by
    have hh := K.mul_mem (K.mul_mem (K.mul_mem hA hBq) (K.inv_mem hA)) (K.inv_mem hBq)
    have he : (a,1)*(b,q₀)*(a,1)⁻¹*(b,q₀)⁻¹=(b,1) := by
      apply Prod.ext
      · change a*b*a⁻¹*b⁻¹=b
        exact commutator_extract
      · change (1*q₀)*1⁻¹*q₀⁻¹=1
        group
    exact he ▸ hh
  have hS3 : ∀c:S3,(c,1)∈K := by
    have hh : Subgroup.closure ({b,a}:Set S3)≤K.comap (MonoidHom.inl S3 Q) := by
      apply (Subgroup.closure_le _).mpr
      intro c hc
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc
      rcases hc with rfl|rfl
      · exact hB
      · exact hA
    rw [generated] at hh
    exact fun c=>hh (Subgroup.mem_top c)
  have hQ : ∀q:Q,((1:S3),q)∈K := by
    have hh : Subgroup.closure (s:Set Q)≤K.comap (MonoidHom.inr S3 Q) := by
      apply (Subgroup.closure_le _).mpr
      intro q hq
      by_cases he:q=q₀
      · subst q
        have hh := K.mul_mem (K.inv_mem hB) hBq
        have he : (b,1)⁻¹*(b,q₀)=((1:S3),q₀) := by
          apply Prod.ext
          · change b⁻¹*b=1
            exact inv_mul_cancel b
          · change (1:Q)⁻¹*q₀=q₀
            rw [inv_one,one_mul]
        change ((1:S3),q₀)∈K
        exact he ▸ hh
      · apply Subgroup.subset_closure
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨q,Finset.mem_erase.mpr ⟨he,hq⟩,rfl⟩))
    rw [hgen] at hh
    exact fun q=>hh (Subgroup.mem_top q)
  have htop : K=⊤ := by
    apply top_unique
    rintro ⟨c,q⟩ _
    have hh := K.mul_mem (hS3 c) (hQ q)
    simpa only [Prod.mk_mul_mk,mul_one,one_mul] using hh
  refine ⟨T,htop,?_⟩
  have hc : T.card≤(s.erase q₀).card+2 :=
    (Finset.card_insert_le _ _).trans
      ((Nat.add_le_add_right (Finset.card_insert_le _ _) 1).trans
        (by have hi : (((s.erase q₀).image (fun q:Q=>((1:S3),q))):Finset (S3×Q)).card≤
              (s.erase q₀).card := Finset.card_image_le
            omega))
  have hpos : 0<s.card := Finset.card_pos.mpr ⟨q₀,hq₀⟩
  rw [Finset.card_erase_of_mem hq₀] at hc
  omega

theorem exists_generating_finset (Q : Type) [Group Q] [Finite Q] :
    ∃T:Finset ((Equiv.Perm (Fin 3))×Q),
      Subgroup.closure (T:Set ((Equiv.Perm (Fin 3))×Q))=⊤ ∧
      T.card≤max 2 (MarkedC4.genRank Q+1) := by
  obtain ⟨s,hs,hgen⟩ := MarkedC4.genRank_spec (G:=Q)
  by_cases he:s=∅
  · have hsingle : Subgroup.closure ({1}:Set Q)=⊤ := by
      apply top_unique
      rw [←hgen,he,Finset.coe_empty]
      exact Subgroup.closure_mono (Set.empty_subset _)
    obtain ⟨T,hT,hcard⟩ := share_nonempty ({1}:Finset Q)
      (by simpa only [Finset.coe_singleton] using hsingle) 1 (Finset.mem_singleton_self _)
    have htwo : T.card≤2 := by simpa only [Finset.card_singleton] using hcard
    exact ⟨T,hT,htwo.trans (le_max_left _ _)⟩
  · obtain ⟨q,hq⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨T,hT,hcard⟩ := share_nonempty s hgen q hq
    exact ⟨T,hT,(hcard.trans_eq (congrArg (fun k=>k+1) hs)).trans (le_max_right _ _)⟩

theorem genRank_le_max (Q : Type) [Group Q] [Finite Q] :
    MarkedC4.genRank ((Equiv.Perm (Fin 3))×Q)≤max 2 (MarkedC4.genRank Q+1) := by
  obtain ⟨T,hgen,hcard⟩ := exists_generating_finset Q
  exact (MarkedC4.genRank_le hgen).trans hcard

end SymmetricSubgroupAsymptotics.SymmetricThreeDirectFactorGenerators
