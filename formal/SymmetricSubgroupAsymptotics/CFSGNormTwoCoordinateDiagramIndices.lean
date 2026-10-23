import SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckStepMatrices

/-! The actual coordinate-base and root-index permutations belonging to
a Cartan diagram symmetry. These preserve every test and coefficient
in the normalized Geck root-step matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramIndices
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCartanDiagramRoots CFSGNormTwoGeckColumns
variable {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hd : ∀ i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (p : Equiv.Perm I) (hA : ∀ i j,A (p i) (p j)=A i j)

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "q₀" => rootPermutation A p hA

def supportPermutation : Equiv.Perm (b₀).support := (s₀).symm.trans (p.trans s₀)

local notation "p₀" => supportPermutation A hd hs hp ho p

theorem supportPermutation_simple (i : I) : p₀ (s₀ i)=s₀ (p i) := by
  simp only [supportPermutation,Equiv.trans_apply,Equiv.symm_apply_apply]

theorem supportPermutation_root (i : (b₀).support) : (p₀ i:Roots A)=q₀ (i:Roots A) := by
  obtain ⟨j,rfl⟩:=(s₀).surjective i
  rw [supportPermutation_simple]
  change coordinateRoot A hd (p j)=q₀ (coordinateRoot A hd j)
  exact (rootPermutation_simple A p hA hd j).symm

theorem rootPermutation_negative (x : Roots A) :
    q₀ (negativeIndex A hs hp x)=negativeIndex A hs hp (q₀ x) := by
  apply Subtype.ext
  simp only [rootPermutation_val,negative_val,map_neg]

theorem root_add_lattice_iff (x y z : Roots A) :
    (rootPairing A hs hp).root x=(rootPairing A hs hp).root y+(rootPairing A hs hp).root z ↔
      x.val=y.val+z.val := by
  have hadd : castVector (y.val+z.val)=castVector y.val+castVector z.val := by
    ext i
    simp only [castVector,Pi.add_apply,Int.cast_add]
  change castVector x.val=castVector y.val+castVector z.val ↔ _
  rw [←hadd,castVector_injective.eq_iff]

theorem rootPermutation_root_add_iff (x y z : Roots A) :
    (rootPairing A hs hp).root (q₀ x)=
      (rootPairing A hs hp).root (q₀ y)+(rootPairing A hs hp).root (q₀ z) ↔
    (rootPairing A hs hp).root x=(rootPairing A hs hp).root y+(rootPairing A hs hp).root z := by
  rw [root_add_lattice_iff,root_add_lattice_iff,rootPermutation_add_iff]

include hA in
theorem supportPermutation_cartan (i j : (b₀).support) :
    (b₀).cartanMatrix (p₀ i) (p₀ j)=(b₀).cartanMatrix i j := by
  obtain ⟨i,rfl⟩:=(s₀).surjective i
  obtain ⟨j,rfl⟩:=(s₀).surjective j
  rw [supportPermutation_simple,supportPermutation_simple,coordinate_cartan,coordinate_cartan]
  exact hA i j

def combinedIndex : Equiv.Perm ((b₀).support⊕Roots A) := Equiv.sumCongr p₀ q₀

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramIndices
