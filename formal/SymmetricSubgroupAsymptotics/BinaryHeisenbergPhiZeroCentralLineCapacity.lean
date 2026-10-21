import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedDisplacementCard
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14GraphHeadRigidity
import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesData
import SymmetricSubgroupAsymptotics.BinaryPairCanonicalCoordinateAction
import SymmetricSubgroupAsymptotics.PermutationCentralizerPointWords
import Mathlib.Data.Fintype.Pi

/-! One scalar constant-line capacity on the original ten kernel coefficients.
Only seven retained scalar constraints and sixteen point words are checked;
there is no enumeration of the256-element inner group or outer lifts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroCentralLineCapacity
local instance heisenbergPhiZeroCentralLinePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev V := Fin 16 → ZMod 2
abbrev K := BinaryHeisenberg14GraphHeadRigidity.stateChart 0
abbrev generators := BinaryHeisenberg14PhiZeroOuterCarries.generators
private def lineInclusion := (binaryRectangularMatrixOfColumnMasks 16 1 (![255] : Fin 1 → ℕ)).mulVecLin
private def lineCoordinates : V →ₗ[ZMod 2] (Fin 1 → ZMod 2) where
  toFun v _ := v 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private theorem line_left (v : Fin 1 → ZMod 2) : lineCoordinates (lineInclusion v)=v := by
  have hb : ∀ j : Fin 1,lineCoordinates (lineInclusion (Pi.single j 1))=Pi.single j 1 := by decide +kernel
  have he : lineCoordinates.comp lineInclusion=LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c=c • Pi.single i (1 : ZMod 2) := by ext j;simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,hb,LinearMap.id_apply]
  exact DFunLike.congr_fun he v
def line : BinaryCoordinateSpace 16 1 := ⟨lineInclusion,lineCoordinates,line_left⟩
def action (i : Fin 6) : V →ₗ[ZMod 2] V := canonicalBinaryLayerAction (generators i)
private def annMasks : Fin 15 → ℕ := ![3,5,9,17,33,65,129,256,512,1024,2048,4096,8192,16384,32768]
private def genIndex : Fin 7 → Fin 6 := ![0,0,1,2,2,3,4]
private def annIndex : Fin 7 → Fin 15 := ![0,2,4,0,2,0,0]
private def inputMasks : Fin 7 → ℕ := ![6,1,2,240,600,408,768]
private def basisMasks : Fin 3 → ℕ := ![776,816,960]
private def coordinateMasks : Fin 10 → ℕ := ![0,0,0,1,2,0,4,0,0,0]
private def combinations : Fin 10 → ℕ := ![2,4,5,0,0,120,0,112,80,16]
private def inclusion := (binaryRectangularMatrixOfColumnMasks 10 3 basisMasks).mulVecLin
private def coordinates := (binaryRectangularMatrixOfColumnMasks 3 10 coordinateMasks).mulVecLin
private theorem chart_basis : ∀ j : Fin 3,coordinates (inclusion (Pi.single j 1))=Pi.single j 1 := by decide +kernel
private theorem chart_left (v : Fin 3 → ZMod 2) : coordinates (inclusion v)=v := by
  have he : coordinates.comp inclusion=LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c=c • Pi.single i (1 : ZMod 2) := by ext j;simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,chart_basis,LinearMap.id_apply]
  exact DFunLike.congr_fun he v
private def chart : BinaryCoordinateSpace 10 3 := ⟨inclusion,coordinates,chart_left⟩
private def input (i : Fin 7) := binaryVectorOfMask 10 (inputMasks i)
private def ann (i : Fin 7) := binaryRowFunctional (binaryVectorOfMask 16 (annMasks (annIndex i)))
private def rowCertificate : BinaryLinearConstraintCertificate input (binaryCoordinateDefectRows chart) where
  support j := Finset.univ.filter fun i => (combinations j).testBit i.val
  target_eq := by decide +kernel
private theorem input_basis : ∀ i : Fin 7,∀ j : Fin 10,
    binaryRowFunctional (input i) (Pi.single j 1)=
      ((ann i).comp ((action (genIndex i)-LinearMap.id).comp K.inclusion)) (Pi.single j 1) := by decide +kernel
private theorem ann_kill_basis : ∀ i : Fin 7,∀ j : Fin 1,
    ann i (line.inclusion (Pi.single j 1))=0 := by decide +kernel
theorem fixed_card_le : Nat.card (binaryCoordinateFixedDisplacements K action line.space)≤8 := by
  apply binaryCoordinateFixedDisplacements_card_le_of_certificate K action line.space ann genIndex chart input rowCertificate
    (fun i => binaryLinearFunctional_ext_basis (input_basis i))
  intro i v hv
  have hle : line.space≤(ann i).ker := line.le_of_basis_mem (ann i).ker (fun j => ann_kill_basis i j)
  exact hle hv
private def candidateImages : Fin 4 → Fin 16 → Fin 16 := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![7,2,1,4,3,6,5,0,15,10,9,12,11,14,13,8],![8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7],![15,10,9,12,11,14,13,8,7,2,1,4,3,6,5,0]]
private theorem candidate_inv : ∀ i j,candidateImages i (candidateImages i j)=j := by decide +kernel
def candidate (i : Fin 4) : Equiv.Perm (Fin 16) := {toFun:=candidateImages i,invFun:=candidateImages i,left_inv:=candidate_inv i,right_inv:=candidate_inv i}
def candidateAction (i : Fin 4) : V →ₗ[ZMod 2] V := canonicalBinaryLayerAction (candidate i)
private theorem allowed_test : ∀ i : Fin 4,
    (∀ j : Fin 10,candidateAction i (K.inclusion (Pi.single j 1))-K.inclusion (Pi.single j 1)∈line.space) → i=0 := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
theorem allowed_card_le : Nat.card {i : Fin 4 // ∀ j : Fin 10,
    candidateAction i (K.inclusion (Pi.single j 1))-K.inclusion (Pi.single j 1)∈line.space}≤1 := by
  letI : Subsingleton {i : Fin 4 // ∀ j : Fin 10,
      candidateAction i (K.inclusion (Pi.single j 1))-K.inclusion (Pi.single j 1)∈line.space} :=
    ⟨fun a b => Subtype.ext ((allowed_test a.val a.property).trans (allowed_test b.val b.property).symm)⟩
  have hc := Nat.card_le_card_of_injective
    (fun _ : {i : Fin 4 // ∀ j : Fin 10,
      candidateAction i (K.inclusion (Pi.single j 1))-K.inclusion (Pi.single j 1)∈line.space} => (() : Unit))
    (fun a b _ => Subsingleton.elim a b)
  simpa only [Nat.card_unique] using hc
private def words : Fin 16 → List (Fin 6) := ![[],[4,2],[2],[4,3],[3],[5,3,2],[3,2],[2,4,2],[0],[4,2,0],[2,0],[4,3,0],[3,0],[5,3,2,0],[3,2,0],[2,4,2,0]]
private theorem word_points : ∀ x : Fin 16,pointWordPermutation generators (words x) 0=x := by decide +kernel
private theorem candidate_test : ∀ y : Fin 16,
    (∀ i : Fin 6,∀ x : Fin 16,pointWordPermutation generators (words (generators i x)) y=
      generators i (pointWordPermutation generators (words x) y)) →
        y=0 ∨ y=7 ∨ y=8 ∨ y=15 := by decide +kernel
private theorem candidate_points : ∀ x : Fin 16,
    pointWordPermutation generators (words x) 0=candidate 0 x ∧
    pointWordPermutation generators (words x) 7=candidate 1 x ∧
    pointWordPermutation generators (words x) 8=candidate 2 x ∧
    pointWordPermutation generators (words x) 15=candidate 3 x := by decide +kernel

theorem centralizer_cases (t : Equiv.Perm (Fin 16)) (ht : ∀ i,Commute t (generators i)) :
    ∃ i : Fin 4,t=candidate i := by
  have hbase : t 0=0 ∨ t 0=7 ∨ t 0=8 ∨ t 0=15 := centralizer_base_mem_of_pointWord_candidates
    generators 0 words word_points {y | y=0 ∨ y=7 ∨ y=8 ∨ y=15} candidate_test t ht
  rcases hbase with h | h | h | h
  · refine ⟨0,Equiv.ext (fun x => ?_)⟩
    rw [centralizer_eq_pointWord_candidate generators 0 words word_points t ht,h]
    exact (candidate_points x).1
  · refine ⟨1,Equiv.ext (fun x => ?_)⟩
    rw [centralizer_eq_pointWord_candidate generators 0 words word_points t ht,h]
    exact (candidate_points x).2.1
  · refine ⟨2,Equiv.ext (fun x => ?_)⟩
    rw [centralizer_eq_pointWord_candidate generators 0 words word_points t ht,h]
    exact (candidate_points x).2.2.1
  · refine ⟨3,Equiv.ext (fun x => ?_)⟩
    rw [centralizer_eq_pointWord_candidate generators 0 words word_points t ht,h]
    exact (candidate_points x).2.2.2
end SymmetricSubgroupAsymptotics.BinaryHeisenbergPhiZeroCentralLineCapacity
