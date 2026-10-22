import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarOpposedScalarCoherence
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveGraph

/-! The two literal coordinate halves of the original split quadratic
space are opposed maximal singular spaces, with nondegenerate cross
pairing. These coordinate facts hold in every characteristic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOpposedSpaces
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexPositiveGraph CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexQuadraticSubspacePoints
variable (K : Type) [Field K]

def negativeSpace (r : ℕ) : Submodule K (Index r→K) where
  carrier := {x | ∀i : Fin r,x (Sum.inl i)=0}
  zero_mem' := fun _=>rfl
  add_mem' := by intro x y hx hy i;simp only [Pi.add_apply,hx i,hy i,add_zero]
  smul_mem' := by intro c x hx i;simp only [Pi.smul_apply,hx i,smul_zero]

def negativeEquiv (r : ℕ) : (Fin r→K)≃ₗ[K]negativeSpace K r where
  toFun x := ⟨Sum.elim 0 x,fun _=>rfl⟩
  invFun x := rightPart K x.val
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    cases i with
    | inl j => exact (x.property j).symm
    | inr j => rfl
  map_add' x y := by
    apply Subtype.ext
    funext i
    cases i with
    | inl j => exact (zero_add (0:K)).symm
    | inr j => rfl
  map_smul' c x := by
    apply Subtype.ext
    funext i
    cases i with
    | inl j => exact (mul_zero c).symm
    | inr j => rfl

def negativeEmbedding (r : ℕ) : (Fin r→K)→ₗ[K](Index r→K) :=
  (negativeSpace K r).subtype.comp (negativeEquiv K r).toLinearMap

theorem negativeSpace_finrank (r : ℕ) : Module.finrank K (negativeSpace K r)=r := by
  simpa using (negativeEquiv K r).finrank_eq.symm

theorem negativeSpace_singular (r : ℕ) (v : Index r→K) (hv : v∈negativeSpace K r) :
    splitQuadraticForm K r v=0 := by
  rw [splitQuadraticForm_apply]
  change (∑i : Fin r,v (Sum.inl i)*v (Sum.inr i))=0
  apply Finset.sum_eq_zero
  intro i _
  rw [hv i,zero_mul]

def positiveSingular (r : ℕ) : Subspaces (splitQuadraticForm K r) :=
  ⟨positiveSpace K r,fun x hx=>positiveSpace_singular K r ⟨x,hx⟩⟩

def negativeSingular (r : ℕ) : Subspaces (splitQuadraticForm K r) :=
  ⟨negativeSpace K r,negativeSpace_singular K r⟩

theorem positive_negative_disjoint (r : ℕ) : Disjoint (positiveSpace K r) (negativeSpace K r) := by
  apply disjoint_iff_inf_le.mpr
  rintro v ⟨hp,hn⟩
  change v=0
  funext i
  cases i with
  | inl j => exact hn j
  | inr j => exact hp j

theorem decompose (r : ℕ) (v : Index r→K) :
    v=positiveEmbedding K r (leftPart K v)+negativeEmbedding K r (rightPart K v) := by
  funext i
  cases i <;> simp [positiveEmbedding,positiveEquiv,negativeEmbedding,negativeEquiv,
    leftPart,rightPart]

theorem cross_positive_nondegenerate (r : ℕ) (y : Index r→K)
    (hy : y∈negativeSpace K r) (hy0 : y≠0) :
    restrictedPairing (splitQuadraticForm K r) (positiveSingular K r) y≠0 := by
  intro hf
  apply hy0
  funext a
  cases a with
  | inl i => exact hy i
  | inr i =>
    have hp : Pi.single (Sum.inl i) (1:K)∈positiveSpace K r := by intro j;simp
    have he := LinearMap.congr_fun hf ⟨Pi.single (Sum.inl i) 1,hp⟩
    change (splitQuadraticForm K r).polarBilin y (Pi.single (Sum.inl i) 1)=0 at he
    rw [splitQuadraticForm_polar] at he
    simpa [polar,leftPart,rightPart,dotProduct,Pi.single_apply] using he

theorem cross_negative_nondegenerate (r : ℕ) (x : Index r→K)
    (hx : x∈positiveSpace K r) (hx0 : x≠0) :
    restrictedPairing (splitQuadraticForm K r) (negativeSingular K r) x≠0 := by
  intro hf
  apply hx0
  funext a
  cases a with
  | inr i => exact hx i
  | inl i =>
    have hn : Pi.single (Sum.inr i) (1:K)∈negativeSpace K r := by intro j;simp
    have he := LinearMap.congr_fun hf ⟨Pi.single (Sum.inr i) 1,hn⟩
    change (splitQuadraticForm K r).polarBilin x (Pi.single (Sum.inr i) 1)=0 at he
    rw [splitQuadraticForm_polar] at he
    simpa [polar,leftPart,rightPart,dotProduct,Pi.single_apply] using he

theorem exists_common_ratio (s : ℕ)
    (f : Points (splitQuadraticForm K (s+3))≃Points (splitQuadraticForm K (s+3)))
    (hlinear : ∀W : Subspaces (splitQuadraticForm K (s+3)),Module.finrank K W.val=s+3 →
      Nonempty (SemilinearPiece (splitQuadraticForm K (s+3)) f W (RingEquiv.refl K)))
    (hfixP : ∀R : Points (splitQuadraticForm K (s+3)),R.val≤positiveSpace K (s+3) → f R=R)
    (hfixZ : ∀R : Points (splitQuadraticForm K (s+3)),R.val≤negativeSpace K (s+3) → f R=R) :
    ∃t : K,t≠0 ∧ ∀x y : Index (s+3)→K,x∈positiveSpace K (s+3) → x≠0 →
      y∈negativeSpace K (s+3) → y≠0 → (splitQuadraticForm K (s+3)).polarBilin y x=0 →
      ∀(hx0 : x+y≠0) (hz : splitQuadraticForm K (s+3) (x+y)=0),
        (f (ray (splitQuadraticForm K (s+3)) (x+y) hx0 hz)).val=Submodule.span K {x+t•y} := by
  exact opposed_common_ratio (splitQuadraticForm K (s+3)) f
    (positiveSingular K (s+3)) (negativeSingular K (s+3))
    (by change 3≤Module.finrank K (positiveSpace K (s+3));rw [positiveSpace_finrank];omega)
    ((negativeSpace_finrank K (s+3)).trans (positiveSpace_finrank K (s+3)).symm)
    (positive_negative_disjoint K (s+3))
    (cross_positive_nondegenerate K (s+3)) (cross_negative_nondegenerate K (s+3))
    (fun W hW=>hlinear W (hW.trans (positiveSpace_finrank K (s+3)))) hfixP hfixZ

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOpposedSpaces
