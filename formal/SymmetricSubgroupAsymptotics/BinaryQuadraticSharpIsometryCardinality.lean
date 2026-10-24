import SymmetricSubgroupAsymptotics.CharacteristicTwoQuadraticLevelProjectiveBound
import SymmetricSubgroupAsymptotics.BinaryQuadraticFunctionalStabilizer

/-! The actual binary quadratic isometry group has order at most 2(q+1)
in characteristic two, by the actual projective-level bound and a
first-column stabilizer of order at most two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.BinaryQuadraticSharpIsometryCardinality

open BinaryQuadraticLevelCardinality BinaryQuadraticIsometryLeadingCardinality
open BinaryQuadraticIsometryCardinality
variable {K : Type*} [Field K]

private theorem fixed_first_entries [CharP K 2] (a b c : K) (hb : b ≠ 0)
    (g : isometries a b c)
    (hg : g.val.val *ᵥ Pi.single (0 : Fin 2) 1 = Pi.single (0 : Fin 2) 1) :
    g.val.val 0 0 = 1 ∧ g.val.val 1 0 = 0 ∧ g.val.val 1 1 = 1 := by
  have h0 : g.val.val 0 0 = 1 := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_same] using congrFun hg 0
  have h1 : g.val.val 1 0 = 0 := by
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using congrFun hg 1
  have hdet := det_eq_one a b c hb g
  rw [Matrix.det_fin_two, h0, h1, one_mul, mul_zero, sub_zero] at hdet
  exact ⟨h0, h1, hdet⟩

private abbrev matrixAction (a b c : K) : MulAction (isometries a b c) (Fin 2 → K) where
  smul g v := g.val.val *ᵥ v
  one_smul v := Matrix.one_mulVec v
  mul_smul g h v := (Matrix.mulVec_mulVec v g.val.val h.val.val).symm

theorem card_le_two_mul_level_card [Finite K] [CharP K 2]
    (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card (isometries a b c) ≤ 2 * Nat.card {v : K × K // eval a b c v = a} := by
  letI : MulAction (isometries a b c) (Fin 2 → K) := matrixAction a b c
  let e0 : Fin 2 → K := Pi.single 0 1
  let O := MulAction.orbit (isometries a b c) e0
  let S := MulAction.stabilizer (isometries a b c) e0
  let encodeOrbit : O → {v : K × K // eval a b c v = a} := fun y =>
    ⟨(y.val 0, y.val 1), by
      obtain ⟨g, hg⟩ := y.property
      change g.val.val *ᵥ e0 = y.val at hg
      change vectorEval a b c y.val = a
      rw [← hg, g.property]
      simp [vectorEval, eval, e0]⟩
  have hOrbitInjective : Function.Injective encodeOrbit := by
    intro y z he
    have hv : (y.val 0, y.val 1) = (z.val 0, z.val 1) :=
      congrArg (fun v : {v : K × K // eval a b c v = a} => v.val) he
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg Prod.fst hv
    · exact congrArg Prod.snd hv
  have hO : Nat.card O ≤ Nat.card {v : K × K // eval a b c v = a} :=
    Nat.card_le_card_of_injective encodeOrbit hOrbitInjective
  let encodeStabilizer : S → {t : K // a * t ^ 2 + b * t + c = c} := fun g =>
    ⟨g.val.val.val 0 1, by
      have hh : g.val.val.val *ᵥ e0 = e0 := by
        exact g.property
      obtain ⟨_, _, h11⟩ := fixed_first_entries a b c hb g.val hh
      have he := g.val.property (Pi.single (1 : Fin 2) 1)
      simpa only [vectorEval, eval, Matrix.mulVec_single_one, Matrix.col_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
        h11, one_pow, mul_one, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,
        add_zero, zero_add] using he⟩
  have hStabilizerInjective : Function.Injective encodeStabilizer := by
    intro g h he
    have h01 : g.val.val.val 0 1 = h.val.val.val 0 1 :=
      congrArg (fun t : {t : K // a * t ^ 2 + b * t + c = c} => t.val) he
    have hg : g.val.val.val *ᵥ e0 = e0 := g.property
    have hh : h.val.val.val *ᵥ e0 = e0 := h.property
    obtain ⟨g00, g10, g11⟩ := fixed_first_entries a b c hb g.val hg
    obtain ⟨h00, h10, h11⟩ := fixed_first_entries a b c hb h.val hh
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · change g.val.val.val 0 0 = h.val.val.val 0 0
      exact g00.trans h00.symm
    · change g.val.val.val 0 1 = h.val.val.val 0 1
      exact h01
    · change g.val.val.val 1 0 = h.val.val.val 1 0
      exact g10.trans h10.symm
    · change g.val.val.val 1 1 = h.val.val.val 1 1
      exact g11.trans h11.symm
  have hS : Nat.card S ≤ 2 :=
    (Nat.card_le_card_of_injective encodeStabilizer hStabilizerInjective).trans
      (quadratic_fibre_card_le_two a b c c ha)
  calc
    Nat.card (isometries a b c) = Nat.card O * Nat.card S := by
      rw [← Nat.card_prod]
      exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (isometries a b c) e0)).symm
    _ ≤ Nat.card {v : K × K // eval a b c v = a} * 2 := Nat.mul_le_mul hO hS
    _ = 2 * Nat.card {v : K × K // eval a b c v = a} := mul_comm _ _


theorem card_le_two_mul_card_add_one_of_leading_ne_zero [Finite K] [CharP K 2]
    (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card (isometries a b c) ≤ 2 * (Nat.card K + 1) :=
  (card_le_two_mul_level_card a b c ha hb).trans
    (Nat.mul_le_mul_left 2
      (CharacteristicTwoQuadraticLevelProjectiveBound.binary_level_card_le_card_add_one a b c a ha))

private def swapBasis : GeneralLinear (K := K) where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    norm_num [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact Matrix.one_fin_two.symm
  inv_val := by
    norm_num [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact Matrix.one_fin_two.symm

private def shearBasis : GeneralLinear (K := K) where
  val := !![1, 0; 1, 1]
  inv := !![1, 0; -1, 1]
  val_inv := by
    norm_num [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact Matrix.one_fin_two.symm
  inv_val := by
    norm_num [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact Matrix.one_fin_two.symm

/-- Every nondegenerate binary quadratic form in characteristic two has
at most twice q+1 many literal linear isometries. -/
theorem card_le_two_mul_card_add_one [Finite K] [CharP K 2]
    (a b c : K) (hb : b ≠ 0) :
    Nat.card (isometries a b c) ≤ 2 * (Nat.card K + 1) := by
  by_cases ha : a ≠ 0
  · exact card_le_two_mul_card_add_one_of_leading_ne_zero a b c ha hb
  by_cases hc : c ≠ 0
  · apply (card_le_of_change_of_basis a b c c b a swapBasis ?_).trans
      (card_le_two_mul_card_add_one_of_leading_ne_zero c b a hc hb)
    intro v
    simp [vectorEval, BinaryQuadraticLevelCardinality.eval, swapBasis,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · have ha0 : a = 0 := not_ne_iff.mp ha
    have hc0 : c = 0 := not_ne_iff.mp hc
    subst a
    subst c
    apply (card_le_of_change_of_basis 0 b 0 b b 0 shearBasis ?_).trans
      (card_le_two_mul_card_add_one_of_leading_ne_zero b b 0 hb hb)
    intro v
    simp [vectorEval, BinaryQuadraticLevelCardinality.eval, shearBasis,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring


variable {F : Type*} [Field F] [Algebra F K]

/-- The genuine functional-preserver subgroup inherits the sharper bound. -/
theorem card_preservers_le_two_mul_card_add_one [Finite K] [CharP K 2]
    (f : Module.Dual F K) (hf : f ≠ 0) (a b c : K) (hb : b ≠ 0) :
    Nat.card (BinaryQuadraticFunctionalStabilizer.preservers f a b c) ≤ 2 * (Nat.card K + 1) := by
  let j : BinaryQuadraticFunctionalStabilizer.preservers f a b c → isometries a b c :=
    fun A => ⟨A.val, BinaryQuadraticFunctionalStabilizer.preserver_isometry f hf a b c A⟩
  have hj : Function.Injective j := by
    intro A B he
    apply Subtype.ext
    exact congrArg (fun g : isometries a b c => g.val) he
  exact (Nat.card_le_card_of_injective j hj).trans (card_le_two_mul_card_add_one a b c hb)

end SymmetricSubgroupAsymptotics.BinaryQuadraticSharpIsometryCardinality
