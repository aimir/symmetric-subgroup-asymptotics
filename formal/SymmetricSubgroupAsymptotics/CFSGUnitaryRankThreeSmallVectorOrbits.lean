import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeScalarComponents
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankOneNonisotropicOrbit

/-! Genuine small-field orbit lower bounds inside the SAME actual
rank-three radical normalizer. Binary singular vectors use all three
scalar components; ternary vectors use two singular components or the
actual nonsingular free-action chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CentralExtensionLayerOrbitIndex

private abbrev vectorOrbit (q : CFSG.PrimePower) (v : Fin 2 → q.Extension 2) :=
  layerOrbit (unitaryRadicalNormalizerVectorAutHom q 1) (Multiplicative.ofAdd v)

theorem rankThree_binary_axis_orbit_card (q : CFSG.PrimePower) (hq : q.order = 2)
    (a : q.Extension 2) (ha : a ≠ 0) :
    9 ≤ Nat.card (vectorOrbit q (Pi.single (0 : Fin 2) a)) := by
  let P := (unitaryConjugateRatioHom q).range × rankOneFixedColumn q
  let f : P → vectorOrbit q (Pi.single (0 : Fin 2) a) := fun p =>
    ⟨Multiplicative.ofAdd (rankOneScalarColumn q ((p.1.val : q.Extension 2) * a) p.2),
      rankThree_ratioRange_scalarColumn_mem q a p.1 p.2⟩
  have hf : Function.Injective f := by
    intro p t he
    apply binary_ratio_scalarColumn_injective q hq a ha
    exact congrArg (fun w : vectorOrbit q (Pi.single (0 : Fin 2) a) => w.val.toAdd) he
  have hP : Nat.card P = 9 := by
    rw [Nat.card_prod, unitaryConjugateRatio_range_card, rankOneFixedColumn_card, hq]
    norm_num
  rw [← hP]
  exact Nat.card_le_card_of_injective f hf

theorem rankThree_two_component_axis_orbit_card (q : CFSG.PrimePower)
    (a : q.Extension 2) (ha : a ≠ 0) :
    2 * (q.order ^ 2 - 1) ≤ Nat.card (vectorOrbit q (Pi.single (0 : Fin 2) a)) := by
  classical
  obtain ⟨z, hz⟩ := exists_unitaryConjugateRatio_not_fixed q
  let zOf (b : Bool) : (unitaryConjugateRatioHom q).range := if b then z else 1
  let f : Bool × rankOneFixedColumn q → vectorOrbit q (Pi.single (0 : Fin 2) a) :=
    fun p => ⟨Multiplicative.ofAdd
      (rankOneScalarColumn q (((zOf p.1).val : q.Extension 2) * a) p.2),
      rankThree_ratioRange_scalarColumn_mem q a (zOf p.1) p.2⟩
  have hf : Function.Injective f := by
    rintro ⟨b,x⟩ ⟨c,y⟩ he
    have hc := congrArg
      (fun w : vectorOrbit q (Pi.single (0 : Fin 2) a) => w.val.toAdd) he
    cases b <;> cases c
    all_goals
      dsimp only [f, zOf] at hc
      simp only [toAdd_ofAdd, Bool.false_eq_true, if_false, if_true,
        OneMemClass.coe_one, Units.val_one, one_mul] at hc
    · change rankOneScalarColumn q a x = rankOneScalarColumn q a y at hc
      exact Prod.ext rfl (rankOneScalarColumn_injective q a ha hc)
    · change rankOneScalarColumn q a x =
        rankOneScalarColumn q ((z.val : q.Extension 2) * a) y at hc
      exact False.elim (hz (scalarColumn_intersection_forces_fixed q a z.val ha x y hc))
    · change rankOneScalarColumn q ((z.val : q.Extension 2) * a) x =
        rankOneScalarColumn q a y at hc
      exact False.elim (hz (scalarColumn_intersection_forces_fixed q a z.val ha y x hc.symm))
    · change rankOneScalarColumn q ((z.val : q.Extension 2) * a) x =
        rankOneScalarColumn q ((z.val : q.Extension 2) * a) y at hc
      exact Prod.ext rfl (rankOneScalarColumn_injective q ((z.val : q.Extension 2) * a)
        (mul_ne_zero (Units.ne_zero z.val) ha) hc)
  have hP : Nat.card (Bool × rankOneFixedColumn q) = 2 * (q.order ^ 2 - 1) := by
    rw [Nat.card_prod, rankOneFixedColumn_card]
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [← hP]
  exact Nat.card_le_card_of_injective f hf

private theorem singular_axis_orbit_le (q : CFSG.PrimePower)
    (v : Fin 2 → q.Extension 2) (hv : v ≠ 0) (hiso : unitaryNaturalPair q 1 v v = 0) :
    ∃ a : q.Extension 2, a ≠ 0 ∧
      Nat.card (vectorOrbit q (Pi.single (0 : Fin 2) a)) ≤ Nat.card (vectorOrbit q v) := by
  obtain ⟨g, a, ha, hg⟩ := exists_rank_one_isotropic_vector_axis q v hv hiso
  have hs : a • (Pi.single (0 : Fin 2) (1 : q.Extension 2)) = Pi.single 0 a := by
    ext i
    fin_cases i <;> simp
  change (g.val.val : Mat (q.Extension 2) 1) *ᵥ v = a • Pi.single (0 : Fin 2) 1 at hg
  rw [hs] at hg
  let t := middleRadicalNormalizerHom q 1 g
  have ht : unitaryRadicalNormalizerVectorAutHom q 1 t (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (Pi.single (0 : Fin 2) a) := by
    change unitaryRadicalNormalizerVectorAutHom q 1 (middleRadicalNormalizerHom q 1 g)
      (Multiplicative.ofAdd v) = _
    rw [middleRadicalNormalizer_vector_action, naturalVectorMulAutHom_apply]
    simp only [toAdd_ofAdd, hg]
  let f : vectorOrbit q (Pi.single (0 : Fin 2) a) → vectorOrbit q v := fun w =>
    ⟨w.val, by
      obtain ⟨u, hu⟩ := w.property
      refine ⟨u * t, ?_⟩
      rw [map_mul]
      change unitaryRadicalNormalizerVectorAutHom q 1 u
        (unitaryRadicalNormalizerVectorAutHom q 1 t (Multiplicative.ofAdd v)) = w.val
      rw [ht, hu]⟩
  have hf : Function.Injective f := by
    intro x y he
    have hv : x.val = y.val := congrArg (fun w : vectorOrbit q v => w.val) he
    exact Subtype.ext hv
  exact ⟨a, ha, Nat.card_le_card_of_injective f hf⟩

theorem rankThree_binary_singular_orbit_card (q : CFSG.PrimePower) (hq : q.order = 2)
    (v : Fin 2 → q.Extension 2) (hv : v ≠ 0) (hiso : unitaryNaturalPair q 1 v v = 0) :
    9 ≤ Nat.card (vectorOrbit q v) := by
  obtain ⟨a, ha, hcard⟩ := singular_axis_orbit_le q v hv hiso
  exact (rankThree_binary_axis_orbit_card q hq a ha).trans hcard

theorem rankThree_ternary_nonzero_orbit_card (q : CFSG.PrimePower) (hq : q.order = 3)
    (v : Fin 2 → q.Extension 2) (hv : v ≠ 0) :
    16 ≤ Nat.card (vectorOrbit q v) := by
  by_cases hiso : unitaryNaturalPair q 1 v v = 0
  · obtain ⟨a, ha, hcard⟩ := singular_axis_orbit_le q v hv hiso
    have h := (rankThree_two_component_axis_orbit_card q a ha).trans hcard
    simpa only [hq] using h
  · have h := rankOne_nonisotropic_normalizer_orbit_card q v hiso
    rw [hq] at h
    exact (by decide : 16 ≤ 3 ^ 2 * (3 - 1)).trans h

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
