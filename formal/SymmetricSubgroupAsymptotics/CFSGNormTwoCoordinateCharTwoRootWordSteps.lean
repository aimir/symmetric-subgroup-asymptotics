import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoColumnRigidity
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterTripleColumns
import Mathlib.Tactic.Module

/-! Actual characteristic-two selected-root steps, transported through
the literal Weyl word used by rootWitness. All signs disappear only
from the already proved signed Weyl-column formula. The root-sum
conditions are literal original lattice/root labels, not a supplied
representation or commutator law. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoRootWordSteps
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckIntegralWord CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateCharTwoColumnRigidity CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoGeckFieldRootSteps CFSGNormTwoGeckFieldOppositionColumns
open CFSGNormTwoCoordinateSelectedRootElement
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i=2)
  (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef) (ho : ∀ i j, i≠j → A i j≤0)
  [Fintype (Roots A)] [DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev Mat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

omit [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible] in
private theorem negative_root (k : Roots A) :
    (rootPairing A hs hp).root (negativeIndex A hs hp k) = -(rootPairing A hs hp).root k := by
  change castVector (negativeIndex A hs hp k).val = -castVector k.val
  rw [CFSGNormTwoGeckColumns.negative_val]
  ext j
  simp only [castVector,Pi.neg_apply,Int.cast_neg]

omit [(rootPairing A hs hp).IsReduced] in
private theorem positive_parameter_add (K : Type) [CommRing K] (i : Fin r) (j k : Roots A)
    (hj : j≠negativeIndex A hs hp (s₀ i))
    (hk : (rootPairing A hs hp).root k =
      (rootPairing A hs hp).root (s₀ i)+(rootPairing A hs hp).root j) (t : K) :
    (canonicalRoot D K false i t : Mat A hd hs hp ho K) *ᵥ Pi.single (.inr j) 1 =
      Pi.single (.inr j) 1+t • Pi.single (.inr k) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_add_step A hs hp b₀ s₀ K i j k hk,second_other A hs hp b₀ s₀ K i j hj,
    smul_zero,add_zero]

private theorem negative_parameter_add (K : Type) [CommRing K] (i : Fin r) (j k : Roots A)
    (hj : j≠(s₀ i : Roots A))
    (hk : (rootPairing A hs hp).root k+(rootPairing A hs hp).root (s₀ i) =
      (rootPairing A hs hp).root j) (t : K) :
    (canonicalRoot D K true i t : Mat A hd hs hp ho K) *ᵥ Pi.single (.inr j) 1 =
      Pi.single (.inr j) 1+t • Pi.single (.inr k) 1 := by
  have hjn : negativeIndex A hs hp j≠negativeIndex A hs hp (s₀ i) := by
    intro he
    apply hj
    apply Subtype.ext
    have hh := congrArg (fun z : Roots A => z.val) he
    dsimp only at hh
    rw [CFSGNormTwoGeckColumns.negative_val,CFSGNormTwoGeckColumns.negative_val] at hh
    exact neg_injective hh
  have hkn : (rootPairing A hs hp).root (negativeIndex A hs hp k) =
      (rootPairing A hs hp).root (s₀ i)+
        (rootPairing A hs hp).root (negativeIndex A hs hp j) := by
    rw [negative_root,negative_root,←hk]
    module
  rw [CFSGNormTwoGeckParameterTripleColumns.negative_val,
    ←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,omega_root,
    positive_parameter_add A hd hs hp ho K i _ _ hjn hkn t,
    Matrix.mulVec_add,Matrix.mulVec_smul,omega_root,omega_root,
    CFSGNormTwoRootNegation.negative_negative,CFSGNormTwoRootNegation.negative_negative]

private theorem inverse_column {I K : Type} [Fintype I] [DecidableEq I] [Field K]
    (W : (Matrix I I K)ˣ) (v u : I → K) (h : (W : Matrix I I K)*ᵥv=u) :
    (↑(W⁻¹) : Matrix I I K)*ᵥu=v := by
  calc
    _ = (↑(W⁻¹) : Matrix I I K)*ᵥ((W : Matrix I I K)*ᵥv) :=
      congrArg (fun x : I → K => (↑(W⁻¹) : Matrix I I K)*ᵥx) h.symm
    _ = v := by
      rw [Matrix.mulVec_mulVec,←Units.val_mul,inv_mul_cancel,Units.val_one,Matrix.one_mulVec]

theorem negative_word_add_step (K : Type) [Field K] [CharP K 2]
    (w : List (Fin r)) (i : Fin r) (j k : Roots A) (hj : j≠(s₀ i : Roots A))
    (hk : (rootPairing A hs hp).root k+(rootPairing A hs hp).root (s₀ i) =
      (rootPairing A hs hp).root j) (t : K) :
    (rootWord D K w true i t : Mat A hd hs hp ho K) *ᵥ
      Pi.single (.inr (wordRoot A hs hp b₀ s₀ w j)) 1 =
      Pi.single (.inr (wordRoot A hs hp b₀ s₀ w j)) 1+
        t • Pi.single (.inr (wordRoot A hs hp b₀ s₀ w k)) 1 := by
  have hwj := word_root_column A hd hs hp ho K w j
  have hwk := word_root_column A hd hs hp ho K w k
  rw [word_eq_canonicalWord] at hwj hwk
  have hwi := inverse_column (canonicalWord D K w) _ _ hwj
  change (((canonicalWord D K w : Mat A hd hs hp ho K)*
      (canonicalRoot D K true i t : Mat A hd hs hp ho K))*
      (↑((canonicalWord D K w)⁻¹) : Mat A hd hs hp ho K))*ᵥ_ = _
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hwi,
    negative_parameter_add A hd hs hp ho K i j k hj hk t,
    Matrix.mulVec_add,Matrix.mulVec_smul,hwj,hwk]

theorem selected_add_step (K : Type) [Field K] [CharP K 2] (beta j k : Roots A)
    (hj : j≠(s₀ (rootWitness A hd hs hp ho beta).val.2 : Roots A))
    (hk : (rootPairing A hs hp).root k+
      (rootPairing A hs hp).root (s₀ (rootWitness A hd hs hp ho beta).val.2) =
        (rootPairing A hs hp).root j) (t : K) :
    (selectedRootElement A hd hs hp ho K beta t : Mat A hd hs hp ho K) *ᵥ
      Pi.single (.inr (wordRoot A hs hp b₀ s₀ (rootWitness A hd hs hp ho beta).val.1 j)) 1 =
      Pi.single (.inr (wordRoot A hs hp b₀ s₀ (rootWitness A hd hs hp ho beta).val.1 j)) 1+
        t • Pi.single (.inr (wordRoot A hs hp b₀ s₀ (rootWitness A hd hs hp ho beta).val.1 k)) 1 :=
  negative_word_add_step A hd hs hp ho K (rootWitness A hd hs hp ho beta).val.1
    (rootWitness A hd hs hp ho beta).val.2 j k hj hk t

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoRootWordSteps
