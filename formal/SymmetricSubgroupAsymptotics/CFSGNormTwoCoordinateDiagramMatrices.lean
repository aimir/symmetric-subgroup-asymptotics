import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramIndices
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-! A genuine Cartan diagram permutation acts on the actual coordinate
Geck matrices by simultaneous basis reindexing. The proof uses the
proved norm-two root-step entries; no source faithfulness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramMatrices
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCartanDiagramRoots CFSGNormTwoGeckColumns CFSGNormTwoGeckStepMatrices
open CFSGNormTwoCoordinateDiagramIndices
variable {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hd : ∀ i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (p : Equiv.Perm I) (hA : ∀ i j,A (p i) (p j)=A i j)

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "p₀" => supportPermutation A hd hs hp ho p
local notation "q₀" => rootPermutation A p hA
local notation "σ" => combinedIndex A hd hs hp ho p hA

theorem stepMatrix_covariance (a : Roots A) (i : (b₀).support) :
    (stepMatrix A hs hp b₀ (q₀ a) (p₀ i)).submatrix σ σ=stepMatrix A hs hp b₀ a i := by
  ext (j|j) (k|k)
  · rfl
  · change (if p₀ j=p₀ i ∧ q₀ k=negativeIndex A hs hp (q₀ a) then (1:ℚ) else 0)=
      if j=i ∧ k=negativeIndex A hs hp a then 1 else 0
    rw [←rootPermutation_negative (A:=A) (hs:=hs) (hp:=hp) (p:=p) (hA:=hA) a]
    simp only [(p₀).injective.eq_iff,(q₀).injective.eq_iff]
  · change (if q₀ j=q₀ a then ((|(b₀).cartanMatrix (p₀ i) (p₀ k)|:ℤ):ℚ) else 0)=
      if j=a then ((|(b₀).cartanMatrix i k|:ℤ):ℚ) else 0
    rw [supportPermutation_cartan (A:=A) (hd:=hd) (hs:=hs) (hp:=hp) (ho:=ho)
      (p:=p) (hA:=hA) i k]
    simp only [(q₀).injective.eq_iff]
  · change (if (rootPairing A hs hp).root (q₀ j)=
        (rootPairing A hs hp).root (q₀ a)+(rootPairing A hs hp).root (q₀ k) then (1:ℚ) else 0)=
      if (rootPairing A hs hp).root j=
        (rootPairing A hs hp).root a+(rootPairing A hs hp).root k then 1 else 0
    simp only [rootPermutation_root_add_iff (A:=A) (hs:=hs) (hp:=hp) (p:=p) (hA:=hA) j a k]

theorem E_covariance (i : (b₀).support) :
    (RootPairing.GeckConstruction.e (p₀ i)).submatrix σ σ=RootPairing.GeckConstruction.e i := by
  rw [E_eq_step A hs hp b₀,E_eq_step A hs hp b₀]
  rw [supportPermutation_root (A:=A) (hd:=hd) (hs:=hs) (hp:=hp) (ho:=ho)
    (p:=p) (hA:=hA) i]
  exact stepMatrix_covariance A hd hs hp ho p hA i i

theorem F_covariance (i : (b₀).support) :
    (RootPairing.GeckConstruction.f (p₀ i)).submatrix σ σ=RootPairing.GeckConstruction.f i := by
  rw [F_eq_step A hs hp b₀,F_eq_step A hs hp b₀]
  rw [supportPermutation_root (A:=A) (hd:=hd) (hs:=hs) (hp:=hp) (ho:=ho)
    (p:=p) (hA:=hA) i,
    ←rootPermutation_negative (A:=A) (hs:=hs) (hp:=hp) (p:=p) (hA:=hA) i]
  exact stepMatrix_covariance A hd hs hp ho p hA (negativeIndex A hs hp i) i

def algebraEquiv : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ≃ₐ[ℚ]
    Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ :=
  Matrix.reindexAlgEquiv ℚ ℚ σ

theorem algebraEquiv_eq_of_covariance
    (M N : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ)
    (h : N.submatrix σ σ=M) : algebraEquiv A hd hs hp ho p hA M=N := by
  ext x y
  obtain ⟨x,rfl⟩:=(σ).surjective x
  obtain ⟨y,rfl⟩:=(σ).surjective y
  change M ((σ).symm (σ x)) ((σ).symm (σ y))=N (σ x) (σ y)
  rw [(σ).symm_apply_apply,(σ).symm_apply_apply]
  exact (congrFun (congrFun h x) y).symm

theorem algebraEquiv_E (i : (b₀).support) :
    algebraEquiv A hd hs hp ho p hA (RootPairing.GeckConstruction.e i)=
      RootPairing.GeckConstruction.e (p₀ i) :=
  algebraEquiv_eq_of_covariance A hd hs hp ho p hA _ _ (E_covariance A hd hs hp ho p hA i)

theorem algebraEquiv_F (i : (b₀).support) :
    algebraEquiv A hd hs hp ho p hA (RootPairing.GeckConstruction.f i)=
      RootPairing.GeckConstruction.f (p₀ i) :=
  algebraEquiv_eq_of_covariance A hd hs hp ho p hA _ _ (F_covariance A hd hs hp ho p hA i)

theorem algebraEquiv_H (i : (b₀).support) :
    algebraEquiv A hd hs hp ho p hA (RootPairing.GeckConstruction.h i)=
      RootPairing.GeckConstruction.h (p₀ i) := by
  rw [←RootPairing.GeckConstruction.lie_e_f_same i,
    ←RootPairing.GeckConstruction.lie_e_f_same (p₀ i)]
  simp only [Ring.lie_def,map_sub,map_mul,algebraEquiv_E,algebraEquiv_F]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramMatrices
