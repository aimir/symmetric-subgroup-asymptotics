import SymmetricSubgroupAsymptotics.SixteenPointNonPairRepresentative
import SymmetricSubgroupAsymptotics.PermutationStabilizerTransport

/-! Arbitrary original point sets in the checked sixteen-point nonpair
representative correspondence. Nonbinaryness is derived from absence of
a pair frame. The point chart is retained for the original normal and
stabilizer transports. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

theorem sixteenPoint_nonpair_original_chart
    {X : Type} [Finite X] (S : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive S X] (hX : Nat.card X = 16)
    (hpair : ¬Nonempty (BinaryPairFrame S (Fin 8))) :
    ∃ U : PreE7NonPairActionClass 16, ∃ points : X ≃ Fin 16,
      relabelSubgroup points S = preE7NonPairAction 16 U := by
  let points : X ≃ Fin 16 := Finite.equivFinOfCardEq hX
  let T := relabelSubgroup points S
  letI : MulAction.IsPretransitive T (Fin 16) := by
    constructor
    intro x y
    obtain ⟨s, hs⟩ := MulAction.exists_smul_eq S (points.symm x) (points.symm y)
    refine ⟨⟨points.permCongr s.1, ⟨s.1, s.2, rfl⟩⟩, ?_⟩
    change points (s.1 (points.symm x)) = y
    change s.1 (points.symm x) = points.symm y at hs
    rw [hs, points.apply_symm_apply]
  have hTpair : ¬Nonempty (BinaryPairFrame T (Fin 8)) := by
    rintro ⟨F⟩
    have hback : relabelSubgroup points.symm T = S := relabelSubgroup_symm points S
    exact hpair ⟨hback ▸ F.relabelPoints points.symm⟩
  have hTnonbinary : ¬ IsPGroup 2 T := by
    intro hT
    apply hTpair
    exact transitiveBinaryPairFrame_nonempty 3 T hT (by norm_num)
  obtain ⟨U, c, hc⟩ := sixteenPoint_nonpair_representative T
    hTnonbinary inferInstance hTpair
  exact ⟨U, points.trans c, (relabelSubgroup_trans points c S).symm.trans hc⟩

structure SixteenPointNonPairOriginalChart
    {X : Type} (S : Subgroup (Equiv.Perm X)) where
  index : PreE7NonPairActionClass 16
  points : X ≃ Fin 16
  matched : relabelSubgroup points S = preE7NonPairAction 16 index

noncomputable def sixteenPointNonPairOriginalChart
    {X : Type} [Finite X] (S : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive S X] (hX : Nat.card X = 16)
    (hpair : ¬Nonempty (BinaryPairFrame S (Fin 8))) :
    SixteenPointNonPairOriginalChart S := by
  let selected := sixteenPoint_nonpair_original_chart S hX hpair
  let U := Classical.choose selected
  let selectedPoints := Classical.choose_spec selected
  exact {
    index := U
    points := Classical.choose selectedPoints
    matched := Classical.choose_spec selectedPoints }

noncomputable def SixteenPointNonPairOriginalChart.groupEquiv
    {X : Type} {S : Subgroup (Equiv.Perm X)}
    (C : SixteenPointNonPairOriginalChart S) :
    S ≃* preE7NonPairAction 16 C.index :=
  (C.points.permCongrHom.subgroupMap S).trans (MulEquiv.subgroupCongr C.matched)

theorem SixteenPointNonPairOriginalChart.groupEquiv_action
    {X : Type} {S : Subgroup (Equiv.Perm X)}
    (C : SixteenPointNonPairOriginalChart S) (s : S) (x : X) :
    C.groupEquiv s • C.points x = C.points (s • x) := by
  change C.points (s.1 (C.points.symm (C.points x))) = C.points (s.1 x)
  rw [C.points.symm_apply_apply]

noncomputable def SixteenPointNonPairOriginalChart.stabilizerEquiv
    {X : Type} {S : Subgroup (Equiv.Perm X)}
    (C : SixteenPointNonPairOriginalChart S) (x : X) :
    MulAction.stabilizer S x ≃*
      MulAction.stabilizer (preE7NonPairAction 16 C.index) (C.points x) where
  toFun s := ⟨C.groupEquiv s.1, by
    change C.groupEquiv s.1 • C.points x = C.points x
    exact (C.groupEquiv_action s.1 x).trans (congrArg C.points s.2)⟩
  invFun t := ⟨C.groupEquiv.symm t.1, by
    change C.groupEquiv.symm t.1 • x = x
    apply C.points.injective
    rw [← C.groupEquiv_action (C.groupEquiv.symm t.1) x, MulEquiv.apply_symm_apply]
    exact t.2⟩
  left_inv s := by
    apply Subtype.ext
    exact C.groupEquiv.symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact C.groupEquiv.apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact C.groupEquiv.map_mul s.1 t.1

theorem SixteenPointNonPairOriginalChart.stabilizerEquiv_commutes
    {X : Type} {S : Subgroup (Equiv.Perm X)}
    (C : SixteenPointNonPairOriginalChart S) (x : X)
    (s : MulAction.stabilizer S x) :
    C.groupEquiv (s : S) =
      (C.stabilizerEquiv x s : preE7NonPairAction 16 C.index) := rfl

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
