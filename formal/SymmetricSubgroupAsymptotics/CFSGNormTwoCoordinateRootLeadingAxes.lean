import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAllRootParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDerivedFirstLayer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightQuotient
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootParametrization
import Mathlib.Tactic.Abel

/-! Actual root groups visible in U's abelianization are precisely the
simple-root axes. Non-simple root parameters have zero leading map by
original integer-degree support, over every coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLeadingAxes
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckColumns CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateLeadingFactor CFSGNormTwoCoordinateDerivedFirstLayer
open CFSGNormTwoCoordinateSimpleRootParametrization CFSGNormTwoRootDegreeSeparation
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem leading_selected_nonsimple (K : Type) [Field K] (k : Roots A)
    (hk : ∀i : Fin r,k≠(s₀ i : Roots A)) (a : K) :
    leadingCoordinates A hd hs hp ho K (selectedRootElement A hd hs hp ho K k a)=0 := by
  funext i
  have hE : selectedFieldCoefficient A hd hs hp ho K k
      (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))=0 := by
    apply selectedFieldCoefficient_support A hd hs hp ho K k
    simp only [latticeWeight,negative_val]
    intro h
    apply hk i
    apply Subtype.ext
    calc
      k.val=(s₀ i : Roots A).val+(-(s₀ i : Roots A).val+k.val) := by abel
      _=(s₀ i : Roots A).val+0 := congrArg (fun v=>(s₀ i : Roots A).val+v) h.symm
      _=(s₀ i : Roots A).val := add_zero _
  have hD : selectedSecondCoefficient A hd hs hp ho K k
      (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))=0 := by
    apply selectedSecondCoefficient_support A hd hs hp ho K k
    simp only [latticeWeight,negative_val]
    intro h
    apply root_val_ne_double A (s₀ i) k
    calc
      (s₀ i : Roots A).val=(s₀ i : Roots A).val+0 := (add_zero _).symm
      _=(s₀ i : Roots A).val+(-(s₀ i : Roots A).val+(k.val+k.val)) :=
        congrArg (fun v=>(s₀ i : Roots A).val+v) h
      _=k.val+k.val := by abel
  change (selectedRootElement A hd hs hp ho K k a : CoordMat A hd hs hp ho K)
    (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))=0
  rw [selectedRootElement_expansion]
  simp only [Matrix.add_apply,Matrix.one_apply,Sum.inl_ne_inr,if_false,
    Matrix.smul_apply,hE,hD,smul_zero,add_zero]

theorem nonsimple_root_subgroup_le_derived (K : Type) [Field K] (k : Roots A)
    (hk : ∀i : Fin r,k≠(s₀ i : Roots A)) :
    (rootSubgroup A hd hs hp ho K k).subgroupOf (PositiveGroup A hd hs hp ho K)≤
      commutator (PositiveGroup A hd hs hp ho K) := by
  intro x hx
  rw [←leading_kernel_eq_derived A hd hs hp ho K,MonoidHom.mem_ker]
  obtain ⟨a,ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x.val).mp hx
  change Multiplicative.ofAdd (leadingCoordinates A hd hs hp ho K x.val)=1
  rw [←ha,leading_selected_nonsimple A hd hs hp ho K k hk a]
  rfl

theorem leading_selected_simple (i : Fin r) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧ ∀(K : Type) [Field K] (a : K),
      leadingCoordinates A hd hs hp ho K (selectedRootElement A hd hs hp ho K (s₀ i) a)=
        (Pi.single i ((ε:K)*a) : Fin r→K) := by
  obtain ⟨ε,hε,he⟩ := selected_simple_root_sign A hd hs hp ho i
  refine ⟨ε,hε,?_⟩
  intro K _ a
  rw [he K a]
  have hh := leadingHom_positiveRoot A hd hs hp ho K i ((ε:K)*a)
  change leadingCoordinates A hd hs hp ho K
    (CFSGSerreQuadraticMatrix.canonicalRoot
      (CFSGNormTwoGeckIntegralRealization.realizationData A hs hp b₀ s₀) K false i ((ε:K)*a))=
        Pi.single i ((ε:K)*a) at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLeadingAxes
