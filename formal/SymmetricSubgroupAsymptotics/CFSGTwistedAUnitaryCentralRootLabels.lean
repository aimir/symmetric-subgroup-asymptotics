import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralRootImage
import SymmetricSubgroupAsymptotics.CFSGUnitaryExtremeConjugation

/-! Exact natural labels for conjugates of the ACTUAL upper centre.
Two such subgroups coincide exactly when their first-column lines do.
The reverse implication uses the signed-form norm multiplier, including
characteristic two. Abstract automorphism recognition is not assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical
open CFSGSerreOrdinaryTwists

def naturalCentralRootHom (q : CFSG.PrimePower) (s : ℕ) :
    Multiplicative (centralParameters q s) →* naturalFixed (s + 2) q :=
  (fixedRadical q s).subtype.comp (centralRadicalHom q s)

def naturalCentralRootLine (q : CFSG.PrimePower) (s : ℕ) :
    Subgroup (naturalFixed (s + 2) q) := (naturalCentralRootHom q s).range

theorem naturalCentralRootLine_eq_center_image (q : CFSG.PrimePower) (s : ℕ) :
    naturalCentralRootLine q s =
      (Subgroup.center (naturalUnipotent (s + 2) q)).map (upperFixedHom q (s + 2)) := by
  rw [naturalUnipotent_center_eq]
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨upperCentralHom q s c, ⟨c, rfl⟩, rfl⟩
  · rintro ⟨u, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩

theorem mem_naturalCentralRootLine_iff (q : CFSG.PrimePower) (s : ℕ)
    (x : naturalFixed (s + 2) q) : x ∈ naturalCentralRootLine q s ↔
      ∃ (b : q.Extension 2) (hb : Condition q s 0 b), x = centralFixed q s b hb := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.toAdd.val, centralParameters_condition q s c.toAdd.val c.toAdd.property, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨Multiplicative.ofAdd ⟨b, (centralCondition_iff q s b).mp hb⟩, rfl⟩

def conjugateNaturalCentralRootLine (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q) : Subgroup (naturalFixed (s + 2) q) :=
  (naturalCentralRootLine q s).map (MulAut.conj g).toMonoidHom

theorem conjugateCentralPoint_eq_span (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q) :
    conjugateCentralPoint q s g =
      (q.Extension 2) ∙ ((g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ
        (Pi.single (0 : Fin (s + 3)) 1)) := by
  rw [conjugateCentralPoint, centralPoint, Submodule.map_span, Set.image_singleton]
  rfl

theorem centralFixed_zero (q : CFSG.PrimePower) (s : ℕ) (h0 : Condition q s 0 0) :
    centralFixed q s 0 h0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change ((centralFixed q s 0 h0).val.val : Mat (q.Extension 2) (s + 2)) = 1
  rw [show ((centralFixed q s 0 h0).val.val : Mat (q.Extension 2) (s + 2)) =
      1 + Matrix.single (0 : Fin (s + 3)) (Fin.last (s + 2)) 0 from
    radicalCentral_matrix q s 0 h0, Matrix.single_zero, add_zero]

theorem centralFixed_parameter_eq_of_eq (q : CFSG.PrimePower) (s : ℕ)
    (b c : q.Extension 2) (hb : Condition q s 0 b) (hc : Condition q s 0 c)
    (he : centralFixed q s b hb = centralFixed q s c hc) : b = c := by
  have hm := congrArg (fun x : naturalFixed (s + 2) q =>
    (x.val.val : Mat (q.Extension 2) (s + 2)) 0 (Fin.last (s + 2))) he
  change ((centralFixed q s b hb).val.val : Mat (q.Extension 2) (s + 2)) 0 (Fin.last (s + 2)) =
    ((centralFixed q s c hc).val.val : Mat (q.Extension 2) (s + 2)) 0 (Fin.last (s + 2)) at hm
  rw [show ((centralFixed q s b hb).val.val : Mat (q.Extension 2) (s + 2)) =
      1 + Matrix.single (0 : Fin (s + 3)) (Fin.last (s + 2)) b from radicalCentral_matrix q s b hb,
    show ((centralFixed q s c hc).val.val : Mat (q.Extension 2) (s + 2)) =
      1 + Matrix.single (0 : Fin (s + 3)) (Fin.last (s + 2)) c from radicalCentral_matrix q s c hc] at hm
  simp only [Matrix.add_apply, Matrix.single_apply_same] at hm
  exact add_left_cancel hm

theorem naturalFixed_signedForm (q : CFSG.PrimePower) (r : ℕ) (k : naturalFixed r q) :
    ((k.val.val : Mat (q.Extension 2) r).map (definingFieldAutomorphism q 2)).transpose *
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *
      (k.val.val : Mat (q.Extension 2) r) =
      (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) :=
  fixed_unit_signedForm (q.Extension 2) r (definingFieldAutomorphism q 2).toRingHom
    k.val.val k.property

theorem conjugateCentralFixed_of_point_eq (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 2) q) (hp : conjugateCentralPoint q s g = conjugateCentralPoint q s h)
    (b : q.Extension 2) (hb : Condition q s 0 b) :
    ∃ (c : q.Extension 2) (hc : Condition q s 0 c),
      g * centralFixed q s b hb * g⁻¹ = h * centralFixed q s c hc * h⁻¹ := by
  let k : naturalFixed (s + 2) q := h⁻¹ * g
  have hform := naturalFixed_signedForm q (s + 2) k
  have hp' := hp
  rw [conjugateCentralPoint_eq_span, conjugateCentralPoint_eq_span] at hp'
  obtain ⟨a, he⟩ := extreme_conjugate_of_span_eq (s + 2) (definingFieldAutomorphism q 2)
    g.val.val h.val.val hform hp' b
  let c := a * definingFieldAutomorphism q 2 a * b
  have hc : Condition q s 0 c := centralParameter_norm_mul_condition q s a b hb
  refine ⟨c, hc, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (g.val.val : Mat (q.Extension 2) (s + 2)) *
      ((centralFixed q s b hb).val.val : Mat (q.Extension 2) (s + 2)) *
      (((g.val.val)⁻¹ : (Mat (q.Extension 2) (s + 2))ˣ) : Mat (q.Extension 2) (s + 2)) =
    (h.val.val : Mat (q.Extension 2) (s + 2)) *
      ((centralFixed q s c hc).val.val : Mat (q.Extension 2) (s + 2)) *
      (((h.val.val)⁻¹ : (Mat (q.Extension 2) (s + 2))ˣ) : Mat (q.Extension 2) (s + 2))
  rw [show ((centralFixed q s b hb).val.val : Mat (q.Extension 2) (s + 2)) =
      1 + Matrix.single (0 : Fin (s + 3)) (Fin.last (s + 2)) b from radicalCentral_matrix q s b hb,
    show ((centralFixed q s c hc).val.val : Mat (q.Extension 2) (s + 2)) =
      1 + Matrix.single (0 : Fin (s + 3)) (Fin.last (s + 2)) c from radicalCentral_matrix q s c hc]
  exact he

theorem conjugateNaturalCentralRootLine_le_of_point_eq (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 2) q) (hp : conjugateCentralPoint q s g = conjugateCentralPoint q s h) :
    conjugateNaturalCentralRootLine q s g ≤ conjugateNaturalCentralRootLine q s h := by
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨b, hb, rfl⟩ := (mem_naturalCentralRootLine_iff q s u).mp hu
  obtain ⟨c, hc, he⟩ := conjugateCentralFixed_of_point_eq q s g h hp b hb
  exact ⟨centralFixed q s c hc, (mem_naturalCentralRootLine_iff q s _).mpr ⟨c, hc, rfl⟩, he.symm⟩

theorem conjugateNaturalCentralRootLine_eq_of_point_eq (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 2) q) (hp : conjugateCentralPoint q s g = conjugateCentralPoint q s h) :
    conjugateNaturalCentralRootLine q s g = conjugateNaturalCentralRootLine q s h :=
  le_antisymm (conjugateNaturalCentralRootLine_le_of_point_eq q s g h hp)
    (conjugateNaturalCentralRootLine_le_of_point_eq q s h g hp.symm)

theorem conjugateCentralPoint_eq_of_rootLine_eq (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 2) q)
    (hL : conjugateNaturalCentralRootLine q s g = conjugateNaturalCentralRootLine q s h) :
    conjugateCentralPoint q s g = conjugateCentralPoint q s h := by
  obtain ⟨b, hb0, hb⟩ := exists_nonzero_central_parameter q s
  have h0 : Condition q s 0 0 :=
    centralParameters_condition q s 0 (centralParameters q s).zero_mem
  have hroot : centralFixed q s b hb ≠ 1 := by
    intro he
    exact hb0 (centralFixed_parameter_eq_of_eq q s b 0 hb h0
      (he.trans (centralFixed_zero q s h0).symm))
  have hnon : g * centralFixed q s b hb * g⁻¹ ≠ 1 := by
    intro he
    exact hroot ((MulAut.conj g).injective (he.trans (MulAut.conj g).map_one.symm))
  have hx : g * centralFixed q s b hb * g⁻¹ ∈ conjugateNaturalCentralRootLine q s h := by
    rw [← hL]
    exact ⟨centralFixed q s b hb, (mem_naturalCentralRootLine_iff q s _).mpr ⟨b, hb, rfl⟩, rfl⟩
  obtain ⟨u, hu, he⟩ := hx
  obtain ⟨c, hc, rfl⟩ := (mem_naturalCentralRootLine_iff q s u).mp hu
  change h * centralFixed q s c hc * h⁻¹ = g * centralFixed q s b hb * g⁻¹ at he
  have hc0 : c ≠ 0 := by
    intro hz
    have hzero : centralFixed q s c hc = 1 := by
      subst c
      exact centralFixed_zero q s hc
    apply hnon
    rw [← he, hzero, mul_one, mul_inv_cancel]
  exact conjugateCentralPoint_eq_of_element_eq q s g h b c hb hc hb0 hc0 he.symm

theorem conjugateNaturalCentralRootLine_eq_iff_point_eq (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 2) q) :
    conjugateNaturalCentralRootLine q s g = conjugateNaturalCentralRootLine q s h ↔
      conjugateCentralPoint q s g = conjugateCentralPoint q s h :=
  ⟨conjugateCentralPoint_eq_of_rootLine_eq q s g h,
    conjugateNaturalCentralRootLine_eq_of_point_eq q s g h⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
