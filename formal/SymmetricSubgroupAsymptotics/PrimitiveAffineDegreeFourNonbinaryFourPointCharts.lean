import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourA4OriginalGroupChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourS4OriginalGroupChart
import Mathlib.GroupTheory.Perm.Subgroup

/-! The two original nonbinary four-point charts are populated internally.
The elementary order/index argument leaves exactly natural A4 and S4. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem nonbinary_fourPoint_eq_alternating_or_top
    (A : Subgroup (Equiv.Perm (Fin 4)))
    [MulAction.IsPretransitive A (Fin 4)] (hnon : ¬ IsPGroup 2 A) :
    A = alternatingGroup (Fin 4) ∨ A = ⊤ := by
  by_cases htop : A = ⊤
  · exact Or.inr htop
  · left
    have hindex : (MulAction.stabilizer A (0 : Fin 4)).index = 4 := by
      simpa only [Nat.card_fin] using
        MulAction.index_stabilizer_of_transitive A (0 : Fin 4)
    have hmul := (MulAction.stabilizer A (0 : Fin 4)).card_mul_index
    rw [hindex] at hmul
    have h4 : 4 ∣ Nat.card A :=
      ⟨Nat.card (MulAction.stabilizer A (0 : Fin 4)), by omega⟩
    have hle : Nat.card A ≤ 24 := by
      have h := Subgroup.card_le_card_group A
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at h ⊢
      exact h
    have hdiv : Nat.card A ∣ 24 := by
      have h := Subgroup.card_subgroup_dvd_card A
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at h ⊢
      exact h
    rw [Nat.card_eq_fintype_card] at hdiv
    have hne24 : Nat.card A ≠ 24 := by
      intro hcard
      apply htop
      apply Subgroup.eq_top_of_card_eq
      rw [hcard]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hnot2 : ¬ IsPGroup 2 A := hnon
    have hcard : Nat.card A = 12 := by
      rcases h4 with ⟨k, hk⟩
      have hkpos : 0 < k := by
        have hpos : 0 < Nat.card A := Nat.card_pos
        omega
      have hk6 : k ≤ 6 := by omega
      interval_cases k
      · exfalso
        apply hnot2
        apply IsPGroup.of_card (n := 2)
        norm_num at hk ⊢
        exact hk
      · exfalso
        apply hnot2
        apply IsPGroup.of_card (n := 3)
        norm_num at hk ⊢
        exact hk
      · norm_num at hk ⊢
        exact hk
      · have hf : Fintype.card A = 16 := by
          simpa [Nat.card_eq_fintype_card] using hk
        rw [hf] at hdiv
        norm_num at hdiv
      · have hf : Fintype.card A = 20 := by
          simpa [Nat.card_eq_fintype_card] using hk
        rw [hf] at hdiv
        norm_num at hdiv
      · exact False.elim (hne24 (by omega))
    have hindexA : A.index = 2 := by
      have h := A.card_mul_index
      have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
        norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
      rw [hcard, hperm] at h
      omega
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    exact hindexA

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)

theorem degreeFour_nonbinary_actual_pointCharts
    (hs : Nat.card block.Points = 4) (hnon : ¬ IsPGroup 2 block.Top) :
    Nonempty (DegreeFourA4OriginalPointChart block) ∨
      Nonempty (DegreeFourS4OriginalPointChart block) := by
  let points : block.Points ≃ Fin 4 := Finite.equivFinOfCardEq hs
  let T := relabelSubgroup points block.Top
  let eG : block.Top ≃* T := points.permCongrHom.subgroupMap block.Top
  let f : MulActionHom eG block.Points (Fin 4) := {
    toFun := points
    map_smul' := by
      intro s x
      change points (s.1 x) = ((points.permCongrHom.subgroupMap block.Top s).1) (points x)
      simp [Equiv.permCongr_apply] }
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  letI : MulAction.IsPretransitive T (Fin 4) :=
    MulAction.IsPretransitive.of_surjective_map (f := f) points.surjective
      (inferInstance : MulAction.IsPretransitive block.Top block.Points)
  have hT : ¬ IsPGroup 2 T := by
    intro hp
    exact hnon (hp.of_injective eG.toMonoidHom eG.injective)
  rcases nonbinary_fourPoint_eq_alternating_or_top T hT with hA | hS
  · exact Or.inl ⟨⟨points, hA⟩⟩
  · exact Or.inr ⟨⟨points, hS⟩⟩

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
