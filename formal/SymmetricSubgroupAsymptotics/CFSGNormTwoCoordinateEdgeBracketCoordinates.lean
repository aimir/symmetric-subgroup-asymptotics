import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleBracketDegrees
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixDistinctDegreeCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrderedPairSingleDegrees

/-! Actual adjacent-edge bracket coefficients are independent over every
field. Sum degrees are separated over the integer coordinate lattice;
nonzero bracket coefficients come from actual Weyl conjugation, so this
does not assume nondegeneracy after reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateEdgeBracketCoordinates
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGGradedMatrixSupport CFSGGradedMatrixDistinctDegreeCoordinates
open CFSGNormTwoGeckSimpleBracketDegrees CFSGOrderedPairSingleDegrees
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

abbrev Edge := {p : Fin r×Fin r // p.1<p.2 ∧ A p.1 p.2= -1}

def edgeDegree (p : Edge A) : Fin r→ℤ :=
  (Pi.single p.val.1 (1:ℤ) : Fin r→ℤ)+Pi.single p.val.2 (1:ℤ)

theorem edgeDegree_injective : Function.Injective (edgeDegree A) := by
  intro p q h
  have hh : (⟨p.val,p.property.1⟩ : {p : Fin r×Fin r // p.1<p.2})=
      ⟨q.val,q.property.1⟩ := pairDegree_injective h
  exact Subtype.ext (congrArg
    (fun z : {p : Fin r×Fin r // p.1<p.2}=>z.val) hh)

variable (hd : ∀i,A i i=2) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "ell" => latticeWeight A hs hp b₀

def edgeBracket (K : Type) [Field K] (p : Edge A) :
    Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K :=
  ⁅fieldRoot D K false p.val.1,fieldRoot D K false p.val.2⁆

theorem edgeBracket_support (K : Type) [Field K] (p : Edge A) :
    Supported ell (fun v=>v+edgeDegree A p) (edgeBracket A hd hs hp ho K p) := by
  exact simple_bracket_support A hs hp b₀ s₀ K p.val.1 p.val.2

theorem edgeBracket_ne_zero (K : Type) [Field K] (p : Edge A) :
    edgeBracket A hd hs hp ho K p≠0 := by
  apply adjacent_bracket_ne_zero A hs hp b₀ s₀ K p.val.1 p.val.2
  change (b₀).cartanMatrix (s₀ p.val.2) (s₀ p.val.1)= -1
  rw [coordinate_cartan_transpose A hd hs hp ho]
  exact p.property.2

theorem edge_coefficients_unique (K : Type) [Field K] (c d : Edge A→K)
    (h : (∑p,c p • edgeBracket A hd hs hp ho K p)=
      ∑p,d p • edgeBracket A hd hs hp ho K p) : c=d := by
  classical
  exact coefficients_unique ell (edgeDegree A) (edgeDegree_injective A)
    (edgeBracket A hd hs hp ho K) (edgeBracket_support A hd hs hp ho K)
    (edgeBracket_ne_zero A hd hs hp ho K) c d h

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateEdgeBracketCoordinates
