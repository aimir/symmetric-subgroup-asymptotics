import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootParametrization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAllRootLines

/-! The literal canonical simple positive parameter subgroup projects
to the SAME original lattice-labelled simple root line. The sign of
the chosen root witness is proved an integral unit and reparametrized. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCanonicalSimpleRootLine
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootElementRange CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateSimpleRootParametrization CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinatePositiveQuotientInjectivity
open CFSGNormTwoCoordinateElementaryRootParameters
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem rootSubgroup_simple_eq_canonical (j : Fin r) :
    rootSubgroup A hd hs hp ho K (s₀ j)=canonicalRootSubgroup D K false j := by
  obtain ⟨ε,hε,he⟩ := selected_simple_root_sign A hd hs hp ho j
  have hεsq : (ε:K)*(ε:K)=1 := by rcases hε with rfl|rfl <;> norm_num
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K (s₀ j) x).mp hx
    exact ⟨(ε:K)*a,(he K a).symm.trans ha⟩
  · rintro ⟨a,rfl⟩
    apply (mem_rootSubgroup_iff_selected A hd hs hp ho K (s₀ j) _).mpr
    refine ⟨(ε:K)*a,?_⟩
    rw [he K ((ε:K)*a),←mul_assoc,hεsq,one_mul]

theorem original_canonical_simple_root_line
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    ((canonicalRootSubgroup D K false j).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
      (originalProjection A hd hs hp ho K i)=
        originalFullRootLine A hd hs hp ho K i (s₀ j) := by
  rw [←rootSubgroup_simple_eq_canonical A hd hs hp ho K j]
  rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCanonicalSimpleRootLine
