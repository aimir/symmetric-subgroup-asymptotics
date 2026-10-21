import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersStepMenu
import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersTransport
import SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainersCover
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-! The actual minimal-block induction step for soluble containers.
The primitive fibre and the smaller top are covered independently; their
full wreath envelope contains every original permutation after recording
the explicit whole-point relabelling. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
open CFSGSolublePrimitiveContainers

theorem subgroup_le_inverse_relabel {X Y : Type} (e : X ≃ Y)
    (G : Subgroup (Equiv.Perm X)) (H : Subgroup (Equiv.Perm Y))
    (h : G.map e.permCongrHom.toMonoidHom ≤ H) :
    G ≤ H.map e.symm.permCongrHom.toMonoidHom := by
  intro g hg
  refine ⟨e.permCongrHom g, h ⟨g, hg, rfl⟩, ?_⟩
  apply Equiv.ext
  intro x
  change e.symm (e (g (e.symm (e x)))) = g x
  simp only [Equiv.symm_apply_apply]

theorem subgroup_relabel_comp {X Y Z : Type} (H : Subgroup (Equiv.Perm X))
    (e : X ≃ Y) (f : Y ≃ Z) :
    (H.map e.permCongrHom.toMonoidHom).map f.permCongrHom.toMonoidHom =
      H.map (e.trans f).permCongrHom.toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem step_covers (n : ℕ)
    (below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val) (hn : 2 ≤ n)
    (U : Subgroup (Equiv.Perm (Fin n))) (hU : IsSolvable U)
    (htrans : MulAction.IsPretransitive U (Fin n)) :
    ∃ i : StepIndex n below, U ≤ stepGroup n below i := by
  letI solubleWreathCover_original : IsSolvable U := hU
  letI solubleWreathCover_transitive : MulAction.IsPretransitive U (Fin n) := htrans
  letI solubleWreathCover_points : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  by_cases hprim : MulAction.IsPreprimitive U (Fin n)
  · letI solubleWreathCover_primitive : MulAction.IsPreprimitive U (Fin n) := hprim
    obtain ⟨i, hi⟩ := primitive_menu_covers n U
    refine ⟨(Sum.inl i, 1), ?_⟩
    change U ≤ (primitiveEnvelope i).map (MonoidHom.id _)
    rw [Subgroup.map_id]
    exact hi
  · let x : Fin n := Classical.choice inferInstance
    obtain ⟨B⟩ := originalMinimalBlock_nonempty (A := U) x hprim
    letI solubleWreathCover_fibreFintype : Fintype B.Fibre := Fintype.ofFinite _
    letI solubleWreathCover_topFintype : Fintype B.Points := Fintype.ofFinite _
    let r := Fintype.card B.Fibre
    let s := Fintype.card B.Points
    let eF : B.Fibre ≃ Fin r := Fintype.equivFin _
    let eI : B.Points ≃ Fin s := Fintype.equivFin _
    have hrs : r * s = n := by
      simpa only [r, s, ← Nat.card_eq_fintype_card, Nat.card_fin] using B.degree_product
    have hr : 2 ≤ r := by
      simpa only [r, ← Nat.card_eq_fintype_card] using B.degrees_ge_two.1
    have hs : 2 ≤ s := by
      simpa only [s, ← Nat.card_eq_fintype_card] using B.degrees_ge_two.2
    have hrlt : r < n := by
      simpa only [r, ← Nat.card_eq_fintype_card, Nat.card_fin] using B.degrees_lt.1
    have hslt : s < n := by
      simpa only [s, ← Nat.card_eq_fintype_card, Nat.card_fin] using B.degrees_lt.2
    let p : FactorPair n := ⟨(⟨r, hrlt⟩, ⟨s, hslt⟩), hr, hs, hrs⟩
    letI solubleWreathCover_component : IsSolvable B.Component :=
      solvable_of_surjective
        (originalBlockFibreAction B.map B.map_equivariant B.base).rangeRestrict_surjective
    letI solubleWreathCover_actualTop : IsSolvable B.Top :=
      solvable_of_surjective B.topMap.rangeRestrict_surjective
    let R := labelledActionImage (A := B.Component) eF
    let T := labelledActionImage (A := B.Top) eI
    letI solubleWreathCover_localFinitePoints : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
    letI solubleWreathCover_localPrimitive : MulAction.IsPreprimitive R (Fin r) :=
      (labelledAction_preprimitive_iff (A := B.Component) eF).mp B.component_preprimitive
    letI solubleWreathCover_localSoluble : IsSolvable R :=
      solvable_of_surjective (labelledActionHom (A := B.Component) eF).rangeRestrict_surjective
    letI solubleWreathCover_topSoluble : IsSolvable T :=
      solvable_of_surjective (labelledActionHom (A := B.Top) eI).rangeRestrict_surjective
    have hTtrans : MulAction.IsPretransitive T (Fin s) :=
      (labelledAction_pretransitive_iff (A := B.Top) eI).mp B.top_pretransitive
    obtain ⟨i, hi⟩ := primitive_menu_covers r R
    obtain ⟨j, hj⟩ := (below p.val.2).covers T inferInstance hTtrans
    let W := wreathEnvelope (primitiveEnvelope i) ((below p.val.2).group j)
    let points := ActualBlockWreathEmbedding.productEquiv B.map B.map_equivariant B.base
    let gamma : Fin n ≃ Fin (r * s) := points.symm.trans (productLabels eF eI)
    have hcoord : labelledActionImage (A := U) gamma ≤ W := by
      exact action_image_le_wreathEnvelope B.Component B.Top eF eI
        (primitiveEnvelope i) ((below p.val.2).group j)
        (fun d => hi ⟨d, rfl⟩) (fun q => hj ⟨q, rfl⟩)
        (ActualBlockWreathEmbedding.embedding B.map B.map_equivariant B.base)
        points (ActualBlockWreathEmbedding.productEquiv_equivariant B.map B.map_equivariant B.base)
    have hmap : U.map gamma.permCongrHom.toMonoidHom ≤ W := by
      rintro _ ⟨g, hg, rfl⟩
      exact hcoord ⟨⟨g, hg⟩, rfl⟩
    have hback := subgroup_le_inverse_relabel gamma U W hmap
    let e : Fin (r * s) ≃ Fin n := finCongr hrs
    let label : Equiv.Perm (Fin n) := e.symm.trans gamma.symm
    let idx : StepIndex n below := (Sum.inr ⟨p, i, j⟩, label)
    refine ⟨idx, ?_⟩
    have he : e.trans label = gamma.symm := by
      ext z
      simp only [label, Equiv.trans_apply, Equiv.symm_apply_apply]
    have hgroup : stepGroup n below idx = W.map gamma.symm.permCongrHom.toMonoidHom := by
      change (W.map e.permCongrHom.toMonoidHom).map label.permCongrHom.toMonoidHom = _
      rw [subgroup_relabel_comp, he]
    rw [hgroup]
    exact hback

end SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
