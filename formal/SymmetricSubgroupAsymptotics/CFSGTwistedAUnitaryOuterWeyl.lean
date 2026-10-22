import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralOpposite

/-! A genuine outer two-root Weyl word in the actual upper/opposite
join sends the last axis to the first axis, with its exact parameter.
Its membership is proved from three actual subgroup elements, not an
assumption that the global reversal lies in the join. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical

theorem single_mulVec_single {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (p q : I) (c : K) (x : I → K) :
    Matrix.single p q c *ᵥ x = Pi.single p (c * x q) := by
  funext i
  simp [Matrix.single_mulVec, Function.update_apply, Pi.single_apply, eq_comm]

theorem extreme_weyl_last_action {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (p q : I) (hpq : p ≠ q) (t b : K) (ht : t ≠ 0) :
    ((1 + Matrix.single p q t) * (1 + Matrix.single q p (-t⁻¹)) *
      (1 + Matrix.single p q t)) *ᵥ Pi.single q b = Pi.single p (t * b) := by
  let A : Matrix I I K := 1 + Matrix.single p q t
  let B : Matrix I I K := 1 + Matrix.single q p (-t⁻¹)
  have hA (x : I → K) : A *ᵥ x = x + Pi.single p (t * x q) := by
    change (1 + Matrix.single p q t) *ᵥ x = _
    rw [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_single]
  have hB (x : I → K) : B *ᵥ x = x + Pi.single q ((-t⁻¹) * x p) := by
    change (1 + Matrix.single q p (-t⁻¹)) *ᵥ x = _
    rw [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_single]
  change (A * B * A) *ᵥ Pi.single q b = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [hA, hB]
  ext i
  by_cases hip : i = p
  · subst i
    simp [Pi.add_apply, hpq, Ne.symm hpq] <;> field_simp [ht] <;> ring <;> simp
  · by_cases hiq : i = q
    · subst i
      simp [Pi.add_apply, hpq, Ne.symm hpq] <;> field_simp [ht] <;> ring <;> simp
    · simp [Pi.add_apply, hip, hiq, hpq, Ne.symm hpq]

def naturalUpperOppositeJoin (q : CFSG.PrimePower) (r : ℕ) :
    Subgroup (NaturalElementary (q.Extension 2) r) :=
  naturalUnipotent r q ⊔ oppositeNaturalUnipotent q r

def outerWeylFixed (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : Condition q s 0 t) : naturalFixed (s + 2) q :=
  centralFixed q s t ht * centralOppositeFixed q s t ht * centralFixed q s t ht

theorem outerWeyl_mem_join (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : Condition q s 0 t) :
    (outerWeylFixed q s t ht).val ∈ naturalUpperOppositeJoin q (s + 2) := by
  have hu : (centralFixed q s t ht).val ∈ naturalUnipotent (s + 2) q :=
    (radicalElement q s 0 t ht).property
  have hU : naturalUnipotent (s + 2) q ≤ naturalUpperOppositeJoin q (s + 2) := le_sup_left
  have hO : oppositeNaturalUnipotent q (s + 2) ≤ naturalUpperOppositeJoin q (s + 2) := le_sup_right
  exact (naturalUpperOppositeJoin q (s + 2)).mul_mem
    ((naturalUpperOppositeJoin q (s + 2)).mul_mem (hU hu)
      (hO (centralOppositeFixed_mem q s t ht))) (hU hu)

theorem outerWeyl_last_action (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : Condition q s 0 t) (ht0 : t ≠ 0) (b : q.Extension 2) :
    ((outerWeylFixed q s t ht).val.val : Mat (q.Extension 2) (s + 2)) *ᵥ
      Pi.single (Fin.last (s + 2)) b = Pi.single 0 (t * b) := by
  have hpq : (0 : Fin (s + 3)) ≠ Fin.last (s + 2) := by
    intro he
    have hv := congrArg (fun i : Fin (s + 3) => i.val) he
    change 0 = s + 2 at hv
    omega
  have hu : ((centralFixed q s t ht).val.val : Mat (q.Extension 2) (s + 2)) =
      1 + Matrix.single (0 : Fin (s + 3)) (Fin.last (s + 2)) t := radicalCentral_matrix q s t ht
  change (((centralFixed q s t ht).val.val : Mat (q.Extension 2) (s + 2)) *
      ((centralOppositeFixed q s t ht).val.val : Mat (q.Extension 2) (s + 2)) *
      ((centralFixed q s t ht).val.val : Mat (q.Extension 2) (s + 2))) *ᵥ _ = _
  rw [hu, centralOpposite_matrix]
  exact extreme_weyl_last_action 0 (Fin.last (s + 2)) hpq t b ht0

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
