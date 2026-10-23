import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarRadicalLine
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySingularPointAction

/-! Literal points of the first totally isotropic two-plane. Their
pairing covectors have the displayed signed last-two-coordinate formula,
and actual root words supply every nonzero vector-line representative.
This is the same point carrier used by the original Aut action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists

theorem unitaryNaturalPair_basis (q : CFSG.PrimePower) (r : ℕ)
    (i : Fin (r + 1)) (x : Fin (r + 1) → q.Extension 2) :
    unitaryNaturalPair q r (Pi.single i 1) x = signWeight (q.Extension 2) r i * x i.rev := by
  have hmap : definingFieldAutomorphism q 2 ∘ (Pi.single i (1 : q.Extension 2)) = Pi.single i 1 := by
    funext j
    by_cases hj : j = i <;> simp only [Function.comp_apply, Pi.single_apply,
      hj, if_true, if_false, map_zero, map_one]
  have hrow : (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) i =
      Pi.single i.rev (signWeight (q.Extension 2) r i) := by
    funext j
    simp only [signedReversalUnit_apply, Pi.single_apply, eq_comm]
  change dotProduct (definingFieldAutomorphism q 2 ∘ Pi.single i 1)
    ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ x) = _
  rw [hmap, single_dotProduct, one_mul]
  change dotProduct ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) i) x = _
  rw [hrow, single_dotProduct]

def starVector (q : CFSG.PrimePower) (s : ℕ) (v : Fin 2 → q.Extension 2) :
    Fin (s + 4) → q.Extension 2 :=
  v 0 • Pi.single (starPositive s 0) 1 + v 1 • Pi.single (starPositive s 1) 1

theorem starVector_positive (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin 2 → q.Extension 2) (i : Fin 2) : starVector q s v (starPositive s i) = v i := by
  have hn : starPositive s 0 ≠ starPositive s 1 := (starPositive_injective s).ne (by decide)
  fin_cases i <;> simp [starVector, hn, Ne.symm hn]

theorem starVector_negative (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin 2 → q.Extension 2) (i : Fin 2) : starVector q s v (starNegative s i) = 0 := by
  simp only [starVector, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
    if_neg (star_coordinates_disjoint s i 0), if_neg (star_coordinates_disjoint s i 1),
    smul_zero, add_zero]

theorem starVector_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (starVector q s) := by
  intro v w h
  ext i
  have hi := congrFun h (starPositive s i)
  simpa only [starVector_positive] using hi

theorem starVector_ne_zero (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin 2 → q.Extension 2) (hv : v ≠ 0) : starVector q s v ≠ 0 := by
  intro h
  apply hv
  apply starVector_injective q s
  simpa only [starVector, Pi.zero_apply, zero_smul, zero_add] using h

theorem starVector_pair (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin 2 → q.Extension 2) (x : Fin (s + 4) → q.Extension 2) :
    unitaryNaturalPair q (s + 3) (starVector q s v) x =
      definingFieldAutomorphism q 2 (v 0) * x (starNegative s 0) -
        definingFieldAutomorphism q 2 (v 1) * x (starNegative s 1) := by
  unfold starVector
  change hermitianPair _ _ (_ + _) x = _
  rw [hermitianPair_add_left]
  have h0 := hermitianPair_smul (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
    (v 0) 1 (Pi.single (starPositive s 0) 1) x
  have h1 := hermitianPair_smul (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
    (v 1) 1 (Pi.single (starPositive s 1) 1) x
  simp only [one_smul, mul_one] at h0 h1
  rw [h0, h1]
  change definingFieldAutomorphism q 2 (v 0) *
      unitaryNaturalPair q (s + 3) (Pi.single (starPositive s 0) 1) x +
    definingFieldAutomorphism q 2 (v 1) *
      unitaryNaturalPair q (s + 3) (Pi.single (starPositive s 1) 1) x = _
  rw [unitaryNaturalPair_basis, unitaryNaturalPair_basis]
  have hs0 : signWeight (q.Extension 2) (s + 3) (starPositive s 0) = 1 := rfl
  have hs1 : signWeight (q.Extension 2) (s + 3) (starPositive s 1) = -1 := by
    change (-1 : q.Extension 2) ^ 1 = -1
    exact pow_one _
  have hr0 : (starPositive s 0).rev = starNegative s 0 := rfl
  have hr1 : (starPositive s 1).rev = starNegative s 1 := rfl
  rw [hs0, hs1, hr0, hr1]
  ring

theorem starVector_pair_zero (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin 2 → q.Extension 2) :
    unitaryNaturalPair q (s + 3) (starVector q s v) (starVector q s w) = 0 := by
  rw [starVector_pair, starVector_negative, starVector_negative, mul_zero, mul_zero, sub_self]

def starPoint (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin 2 → q.Extension 2) (hv : v ≠ 0) : unitarySingularPoints q s :=
  ⟨(q.Extension 2) ∙ starVector q s v, finrank_span_singleton (starVector_ne_zero q s v hv), by
    intro x hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    rw [← ha]
    change hermitianPair _ _ (a • _) (a • _) = 0
    rw [hermitianPair_smul]
    change definingFieldAutomorphism q 2 a * a *
      unitaryNaturalPair q (s + 3) (starVector q s v) (starVector q s v) = 0
    rw [starVector_pair_zero, mul_zero]⟩

theorem exists_starVector_representative (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin 2 → q.Extension 2) (hv : v ≠ 0) :
    ∃ (g : naturalFixed (s + 3) q) (a : q.Extension 2), a ≠ 0 ∧
      unitaryCentralVector q s g = a • starVector q s v := by
  obtain ⟨h, a, ha, he⟩ := exists_isotropic_vector_axis q (s + 1)
    (starVector q s v) (starVector_ne_zero q s v hv) (starVector_pair_zero q s v v)
  have hh := congrArg (fun x : Fin (s + 4) → q.Extension 2 =>
    (↑(h.val.val⁻¹) : Mat (q.Extension 2) (s + 3)) *ᵥ x) he
  have hx : starVector q s v = a • unitaryCentralVector q s h⁻¹ := by
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_smul] using hh
  refine ⟨h⁻¹, a⁻¹, inv_ne_zero ha, ?_⟩
  calc
    unitaryCentralVector q s h⁻¹ = a⁻¹ • (a • unitaryCentralVector q s h⁻¹) := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = a⁻¹ • starVector q s v := congrArg (fun x => a⁻¹ • x) hx.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
