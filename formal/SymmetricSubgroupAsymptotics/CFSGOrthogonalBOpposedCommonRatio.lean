import SymmetricSubgroupAsymptotics.CFSGPolarOpposedScalarCoherence
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleProbes

/-! On the SAME original B positive and negative spaces, maximal-space
linearity and pointwise fixation force one common mixed scalar.
All dimensions, disjointness and cross-pairing nondegeneracy are proved
from the original coordinates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedCommonRatio
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBOpposedGraphShear CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBZeroMiddleProbes CFSGOrthogonalBIntrinsicLongRoots CFSGPolarSubspacePoints
variable (K : Type) [Field K] [Finite K]

def negativeSingular (n : ℕ) : Subspaces (gram K n).toBilin' :=
  ⟨negativeSubspace K n,by
    rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩
    simp [gram_pairing_coordinates,positivePart,negativePart,negativeEmbedding,pos,neg,middle]⟩

theorem negative_finrank (n : ℕ) : Module.finrank K (negativeSubspace K n)=n := by
  have hi : Function.Injective (negativeEmbedding K n) := by
    intro x y h
    exact funext (fun i=>congrFun h (neg n i))
  let e := LinearEquiv.ofInjective (negativeEmbedding K n) hi
  simpa only [Module.finrank_pi,Module.finrank_self,Fintype.card_fin,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one] using e.finrank_eq.symm

theorem positive_negative_disjoint (n : ℕ) :
    Disjoint (positiveSubspace K n) (negativeSubspace K n) := by
  apply disjoint_iff_inf_le.mpr
  rintro v ⟨hp,⟨a,rfl⟩⟩
  change negativeEmbedding K n a=0
  have ha : a=0 := funext (fun i=>(mem_positiveSubspace K n _).mp hp |>.1 i)
  rw [ha,map_zero]

theorem exists_common_ratio (h2 : (2 : K)≠0) (s : ℕ)
    (f : Points (gram K (s+3)).toBilin'≃Points (gram K (s+3)).toBilin')
    (hlinear : ∀W : Subspaces (gram K (s+3)).toBilin',Module.finrank K W.val=s+3 →
      Nonempty (SemilinearPiece (gram K (s+3)).toBilin' f W (RingEquiv.refl K)))
    (hfixP : ∀R : Points (gram K (s+3)).toBilin',R.val≤positiveSubspace K (s+3) → f R=R)
    (hfixZ : ∀R : Points (gram K (s+3)).toBilin',R.val≤negativeSubspace K (s+3) → f R=R) :
    ∃t : K,t≠0 ∧ ∀(x y : Index (s+3)→K),x∈positiveSubspace K (s+3) → x≠0 →
      y∈negativeSubspace K (s+3) → y≠0 → (gram K (s+3)).toBilin' y x=0 →
      ∀(hx0 : x+y≠0) (hz : (gram K (s+3)).toBilin' (x+y) (x+y)=0),
        (f (ray (gram K (s+3)).toBilin' (x+y) hx0 hz)).val=Submodule.span K {x+t•y} := by
  let B := (gram K (s+3)).toBilin'
  let P : Subspaces B := ⟨positiveSubspace K (s+3),positiveSubspace_singular K (s+3)⟩
  let Z := negativeSingular K (s+3)
  have hdP : Module.finrank K P.val=s+3 := positiveSubspace_finrank K (s+3)
  have hdZ : Module.finrank K Z.val=Module.finrank K P.val :=
    (negative_finrank K (s+3)).trans hdP.symm
  have hnP : ∀y∈Z.val,y≠0 → restrictedPairing B P y≠0 := by
    intro y hy hy0 hf
    obtain ⟨a,rfl⟩ := hy
    apply hy0
    have ha : a=0 := by
      funext i
      have he := LinearMap.congr_fun hf
        ⟨Pi.single (pos (s+3) i) 1,positive_basis_mem K _ i⟩
      change B (negativeEmbedding K (s+3) a) (Pi.single (pos (s+3) i) 1)=0 at he
      rw [pairing_positive] at he
      exact (mul_eq_zero.mp he).resolve_left h2
    rw [ha,map_zero]
  have hnZ : ∀x∈P.val,x≠0 → restrictedPairing B Z x≠0 := by
    intro x hx hx0 hf
    obtain ⟨a,rfl⟩ := hx
    apply hx0
    have ha : a=0 := by
      funext i
      have he := LinearMap.congr_fun hf
        ⟨Pi.single (neg (s+3) i) 1,negative_basis_mem K _ i⟩
      change B (positiveEmbedding K (s+3) a) (Pi.single (neg (s+3) i) 1)=0 at he
      rw [pairing_negative] at he
      exact (mul_eq_zero.mp he).resolve_left h2
    rw [ha,map_zero]
  exact opposed_common_ratio B (fun x y=>gram_pairing_symmetric (s+3) x y) f P Z
    (by rw [hdP];omega) hdZ (positive_negative_disjoint K (s+3)) hnP hnZ
    (fun W hW=>hlinear W (hW.trans hdP)) hfixP hfixZ

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedCommonRatio
