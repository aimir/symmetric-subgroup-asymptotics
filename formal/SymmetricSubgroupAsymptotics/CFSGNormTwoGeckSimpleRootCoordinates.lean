import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPrimitiveRootEntry
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
import Mathlib.Tactic.Abel

/-! Literal coordinate functionals separate the original simple Geck
root operators over EVERY coefficient field. This supplies genuine
leading-term uniqueness without a dimension or recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleRootCoordinates
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPrimitiveRootEntry
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckColumns
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s

theorem field_E_unit_entry (K : Type) [CommRing K] (i : Fin r) :
    fieldRoot D K false i (Sum.inl (s i))
      (Sum.inr (negativeIndex A hs hp (s i)))=1 := by
  change (CFSGGeckIntegralMatrices.E b (s i) (Sum.inl (s i))
    (Sum.inr (negativeIndex A hs hp (s i))):K)=1
  rw [integer_E_unit_entry A hs hp b (s i),Int.cast_one]

theorem field_E_coordinate_entry (K : Type) [CommRing K] (i j : Fin r) :
    fieldRoot D K false j (Sum.inl (s i))
      (Sum.inr (negativeIndex A hs hp (s i)))=if i=j then 1 else 0 := by
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    exact field_E_unit_entry A hs hp b s K i
  · rw [if_neg hij]
    apply field_E_lattice_support A hs hp b s K j
    change (0 : n→ℤ)≠(negativeIndex A hs hp (s i)).val+(s j:Roots A).val
    rw [negative_val]
    intro he
    apply hij
    apply s.injective
    apply Subtype.ext
    apply Subtype.ext
    calc
      _=0+(s i:Roots A).val := by abel
      _=(-(s i:Roots A).val+(s j:Roots A).val)+(s i:Roots A).val :=
        congrArg (fun v : n→ℤ=>v+(s i:Roots A).val) he
      _=_ := by abel

theorem simple_sum_coordinate (K : Type) [Field K] (c : Fin r→K) (i : Fin r) :
    (∑j,c j • fieldRoot D K false j) (Sum.inl (s i))
      (Sum.inr (negativeIndex A hs hp (s i)))=c i := by
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply,field_E_coordinate_entry A hs hp b s K,smul_eq_mul]
  simp [mul_ite]

theorem simple_coefficients_unique (K : Type) [Field K] (c d : Fin r→K)
    (h : (∑i,c i • fieldRoot D K false i)=∑i,d i • fieldRoot D K false i) : c=d := by
  funext i
  have hh := congrArg (fun M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K=>
    M (Sum.inl (s i)) (Sum.inr (negativeIndex A hs hp (s i)))) h
  dsimp only at hh
  rw [simple_sum_coordinate,simple_sum_coordinate] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleRootCoordinates
