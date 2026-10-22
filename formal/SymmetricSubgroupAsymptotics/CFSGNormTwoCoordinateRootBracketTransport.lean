import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootBracketUnit

/-! Integral and arbitrary-characteristic transport of the ACTUAL unit
coefficient in a simple-root/positive-root bracket. The sign is chosen
over the original integer lattice once, before any base change. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootBracketTransport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckNegativeWordCoefficients CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootWordString CFSGNormTwoCoordinateSelectedRootLine
open CFSGNormTwoCoordinateRaisedRoot CFSGNormTwoCoordinateRootBracketUnit
open CFSGNormTwoGeckRationalAdjointStrings
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K
local notation "MatZ" => CoordMat A hd hs hp ho ℤ
local notation "MatQ" => CoordMat A hd hs hp ho ℚ

def selectedFieldCoefficient (K : Type) [CommRing K] (k : Roots A) :
    CoordMat A hd hs hp ho K :=
  (Int.castRingHom K).mapMatrix (integerSelectedCoefficient A hd hs hp ho k)

theorem selectedFieldCoefficient_rat (k : Roots A) :
    selectedFieldCoefficient A hd hs hp ho ℚ k=selectedCoefficient A hd hs hp ho k :=
  cast_integerSelectedCoefficient A hd hs hp ho k

theorem selectedFieldCoefficient_eq_first (K : Type) [Field K] (k : Roots A) :
    selectedFieldCoefficient A hd hs hp ho K k=
      firstCoefficient A hs hp b₀ s₀ K (rootWitness A hd hs hp ho k).val.1
        (rootWitness A hd hs hp ho k).val.2 := by
  simp only [selectedFieldCoefficient,integerSelectedCoefficient,firstCoefficient,
    CFSGAlgebraConjugationAction.action_apply,map_mul,cast_integer_word,
    cast_integer_word_inverse] <;> rfl

theorem selectedFieldCoefficient_ne_zero (K : Type) [Field K] (k : Roots A) :
    selectedFieldCoefficient A hd hs hp ho K k≠0 := by
  rw [selectedFieldCoefficient_eq_first]
  exact first_ne_zero A hs hp b₀ s₀ K
    (rootWitness A hd hs hp ho k).val.1 (rootWitness A hd hs hp ho k).val.2

theorem integer_simple_root_bracket_sign (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧
      ⁅CFSGGeckIntegralMatrices.E b₀ (s₀ i),integerSelectedCoefficient A hd hs hp ho k⁆=
        ε • integerSelectedCoefficient A hd hs hp ho (raisedRoot A hd hs hp ho k i hpair) := by
  obtain ⟨ε,hε,h⟩ := simple_root_bracket_sign A hd hs hp ho k hk i hpair
  refine ⟨ε,hε,?_⟩
  have hcast : (Int.castRingHom ℚ).mapMatrix
      ⁅CFSGGeckIntegralMatrices.E b₀ (s₀ i),integerSelectedCoefficient A hd hs hp ho k⁆=
      (ε:ℚ) • (Int.castRingHom ℚ).mapMatrix
        (integerSelectedCoefficient A hd hs hp ho (raisedRoot A hd hs hp ho k i hpair)) := by
    simpa only [Ring.lie_def,map_sub,map_mul,CFSGGeckIntegralMatrices.map_E,
      cast_integerSelectedCoefficient,rational_E_eq,CFSGGeckSerreRepresentation.E] using h
  apply Matrix.ext
  intro a b
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  have he := congrArg (fun M : MatQ=>M a b) hcast
  change (⁅CFSGGeckIntegralMatrices.E b₀ (s₀ i),
    integerSelectedCoefficient A hd hs hp ho k⁆ a b:ℚ)=
      (ε:ℚ)*(integerSelectedCoefficient A hd hs hp ho
        (raisedRoot A hd hs hp ho k i hpair) a b:ℚ) at he
  simpa only [Matrix.smul_apply,zsmul_eq_mul,Int.cast_mul] using he

theorem all_ring_simple_root_bracket_sign (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧ ∀(K : Type) [CommRing K],
      ⁅fieldRoot D K false i,selectedFieldCoefficient A hd hs hp ho K k⁆=
        (ε:K) • selectedFieldCoefficient A hd hs hp ho K
          (raisedRoot A hd hs hp ho k i hpair) := by
  obtain ⟨ε,hε,h⟩ := integer_simple_root_bracket_sign A hd hs hp ho k hk i hpair
  refine ⟨ε,hε,?_⟩
  intro K _
  have he := congrArg (fun M : MatZ=>(Int.castRingHom K).mapMatrix M) h
  simp only [Ring.lie_def,map_sub,map_mul] at he
  have hE : (Int.castRingHom K).mapMatrix (CFSGGeckIntegralMatrices.E b₀ (s₀ i))=
      fieldRoot D K false i := rfl
  rw [hE] at he
  change ⁅fieldRoot D K false i,selectedFieldCoefficient A hd hs hp ho K k⁆=
    (ε:K) • selectedFieldCoefficient A hd hs hp ho K
      (raisedRoot A hd hs hp ho k i hpair)
  rw [Ring.lie_def]
  refine he.trans ?_
  apply Matrix.ext
  intro a b
  change ((ε * integerSelectedCoefficient A hd hs hp ho
      (raisedRoot A hd hs hp ho k i hpair) a b:ℤ):K)=
    (ε:K)*(integerSelectedCoefficient A hd hs hp ho
      (raisedRoot A hd hs hp ho k i hpair) a b:K)
  exact Int.cast_mul _ _

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootBracketTransport
