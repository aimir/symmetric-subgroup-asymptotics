import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalRootColumn
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortParameterWeyl

/-! The literal short orbit restricts to its outer-zero adjoint triple
as a single quadratic rank-one root unit. The other two orthogonal
factors fix all three columns, including in characteristics two and
three. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortAdjointTriple
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedRootWords CFSGTrialityFixedWeylWords
open CFSGNormTwoGeckColumns CFSGNormTwoGeckParameterTripleColumns
open CFSGNormTwoGeckOrthogonalRootColumn CFSGIntegerMatrixPairing
open CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
local instance : DecidableEq (Roots (CartanMatrix.D 4)) := Classical.decEq _
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite

def tripleCartan (K : Type) [Field K] : GeckIndex→K := Pi.single (Sum.inl (Index 0)) 1
def triplePositive (K : Type) [Field K] : GeckIndex→K :=
  Pi.single (Sum.inr (Index 0 : Roots A)) 1
def tripleNegative (K : Type) [Field K] : GeckIndex→K :=
  Pi.single (Sum.inr (negativeIndex A hs hp (Index 0))) 1

private theorem outer_pairing_zero (i : Fin 3) (hi : i≠0) :
    integerPairing A (Index (outerNode i) : Roots A).val (Index 0 : Roots A).val=0 := by
  change integerPairing A (Pi.single (outerNode i) (1:ℤ) : Fin 4→ℤ)
    (Pi.single 0 (1:ℤ) : Fin 4→ℤ)=0
  fin_cases i
  · exact False.elim (hi rfl)
  · decide
  · decide

private theorem other_outer_cartan (K : Type) [Field K] (i : Fin 3) (hi : i≠0)
    (neg : Bool) (t : K) :
    (canonicalRoot rawData K neg (outerNode i) t : Matrix GeckIndex GeckIndex K)*ᵥ
      tripleCartan K=tripleCartan K := by
  have hc : Base.cartanMatrix (Index (outerNode i)) (Index 0)=0 := by
    change CFSGGeckSerreRepresentation.cartan Base Index 0 (outerNode i)=0
    rw [cartan_eq]
    fin_cases i
    · exact False.elim (hi rfl)
    · decide
    · decide
  cases neg
  · simpa only [hc,abs_zero,Int.cast_zero,mul_zero,zero_smul,add_zero] using
      positive_cartan_general A hs hp Base Index K (outerNode i) (Index 0) t
  · simpa only [hc,abs_zero,Int.cast_zero,mul_zero,zero_smul,add_zero] using
      negative_cartan_general A hs hp Base Index K (outerNode i) (Index 0) t

private theorem other_outer_roots (K : Type) [Field K] (i : Fin 3) (hi : i≠0)
    (neg : Bool) (t : K) :
    ((canonicalRoot rawData K neg (outerNode i) t : Matrix GeckIndex GeckIndex K)*ᵥ
      triplePositive K=triplePositive K)∧
    ((canonicalRoot rawData K neg (outerNode i) t : Matrix GeckIndex GeckIndex K)*ᵥ
      tripleNegative K=tripleNegative K) := by
  have hpos := outer_pairing_zero i hi
  have hneg : integerPairing A (Index (outerNode i) : Roots A).val
      (negativeIndex A hs hp (Index 0)).val=0 := by
    rw [CFSGNormTwoGeckColumns.negative_val,map_neg,hpos,neg_zero]
  cases neg
  · exact ⟨positive_fixes_orthogonal_column A hs hp Base Index K _ _ hpos t,
      positive_fixes_orthogonal_column A hs hp Base Index K _ _ hneg t⟩
  · exact ⟨negative_fixes_orthogonal_column A hs hp Base Index K _ _ hpos t,
      negative_fixes_orthogonal_column A hs hp Base Index K _ _ hneg t⟩

theorem shortOrbit_triple_restriction (K : Type) [Field K] (sigma : K≃+*K)
    (neg : Bool) (t : K) :
    ((shortOrbit K sigma neg t : Matrix GeckIndex GeckIndex K)*ᵥtripleCartan K=
      (canonicalRoot rawData K neg 0 t : Matrix GeckIndex GeckIndex K)*ᵥtripleCartan K)∧
    ((shortOrbit K sigma neg t : Matrix GeckIndex GeckIndex K)*ᵥtriplePositive K=
      (canonicalRoot rawData K neg 0 t : Matrix GeckIndex GeckIndex K)*ᵥtriplePositive K)∧
    ((shortOrbit K sigma neg t : Matrix GeckIndex GeckIndex K)*ᵥtripleNegative K=
      (canonicalRoot rawData K neg 0 t : Matrix GeckIndex GeckIndex K)*ᵥtripleNegative K) := by
  have hc1 := other_outer_cartan K 1 (by decide) neg (sigma t)
  have hc2 := other_outer_cartan K 2 (by decide) neg (sigma (sigma t))
  have hr1 := other_outer_roots K 1 (by decide) neg (sigma t)
  have hr2 := other_outer_roots K 2 (by decide) neg (sigma (sigma t))
  change (canonicalRoot rawData K neg 2 (sigma t) : Matrix GeckIndex GeckIndex K)*ᵥ
    tripleCartan K=tripleCartan K at hc1
  change (canonicalRoot rawData K neg 3 (sigma (sigma t)) : Matrix GeckIndex GeckIndex K)*ᵥ
    tripleCartan K=tripleCartan K at hc2
  change ((canonicalRoot rawData K neg 2 (sigma t) : Matrix GeckIndex GeckIndex K)*ᵥ
    triplePositive K=triplePositive K)∧
    ((canonicalRoot rawData K neg 2 (sigma t) : Matrix GeckIndex GeckIndex K)*ᵥ
      tripleNegative K=tripleNegative K) at hr1
  change ((canonicalRoot rawData K neg 3 (sigma (sigma t)) : Matrix GeckIndex GeckIndex K)*ᵥ
    triplePositive K=triplePositive K)∧
    ((canonicalRoot rawData K neg 3 (sigma (sigma t)) : Matrix GeckIndex GeckIndex K)*ᵥ
      tripleNegative K=tripleNegative K) at hr2
  simp only [shortOrbit,Units.val_mul,←Matrix.mulVec_mulVec,hc2,hc1,hr2.1,hr1.1,hr2.2,hr1.2,
    and_self]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortAdjointTriple
