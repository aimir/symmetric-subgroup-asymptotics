import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedCommonRatio
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNegativeDilation

/-! The actual polar map, once linear on maximal spaces and fixed on
both opposed coordinate spaces, agrees with ONE negative dilation on
EVERY zero-middle singular point. Pure points and all mixed supports
are retained. Square realization and the remaining point kernel are
separate from this theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleDilation
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBOpposedGraphShear CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBOpposedCommonRatio CFSGOrthogonalBIntrinsicLongRoots CFSGPolarSubspacePoints
open CFSGOrthogonalBNegativeDilation
variable (K : Type) [Field K] [Finite K]

theorem exists_dilation (h2 : (2 : K)≠0) (s : ℕ)
    (f : Points (gram K (s+3)).toBilin'≃Points (gram K (s+3)).toBilin')
    (hlinear : ∀W : Subspaces (gram K (s+3)).toBilin',Module.finrank K W.val=s+3 →
      Nonempty (SemilinearPiece (gram K (s+3)).toBilin' f W (RingEquiv.refl K)))
    (hfixP : ∀R : Points (gram K (s+3)).toBilin',R.val≤positiveSubspace K (s+3) → f R=R)
    (hfixZ : ∀R : Points (gram K (s+3)).toBilin',R.val≤negativeSubspace K (s+3) → f R=R) :
    ∃t : K,t≠0 ∧ ∀(v : Index (s+3)→K) (hv0 : v≠0)
      (hv : (gram K (s+3)).toBilin' v v=0),v (middle (s+3))=0 →
        (f (ray (gram K (s+3)).toBilin' v hv0 hv)).val=
          Submodule.span K {CFSGOrthogonalBNegativeDilation.map K (s+3) t v} := by
  obtain ⟨t,ht,htr⟩ := exists_common_ratio K h2 s f hlinear hfixP hfixZ
  refine ⟨t,ht,?_⟩
  intro v hv0 hv hm
  let B := (gram K (s+3)).toBilin'
  let x := positiveEmbedding K (s+3) (positivePart K (s+3) v)
  let y := negativeEmbedding K (s+3) (negativePart K (s+3) v)
  have hx : x∈positiveSubspace K (s+3) := ⟨_,rfl⟩
  have hy : y∈negativeSubspace K (s+3) := ⟨_,rfl⟩
  have he : v=x+y := decompose K (s+3) v hm
  have hemap : CFSGOrthogonalBNegativeDilation.map K (s+3) t v=x+t•y := map_decompose K (s+3) t v hm
  let R := ray B v hv0 hv
  by_cases hx0 : x=0
  · have hvy : v=y := by simpa only [hx0,zero_add] using he
    have hRy : R.val≤negativeSubspace K (s+3) := by
      apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      rw [hvy]
      exact hy
    rw [hfixZ R hRy]
    change Submodule.span K {v}=Submodule.span K {CFSGOrthogonalBNegativeDilation.map K (s+3) t v}
    rw [hemap,hx0,zero_add,←hvy]
    exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ht) v).symm
  by_cases hy0 : y=0
  · have hvx : v=x := by simpa only [hy0,add_zero] using he
    have hRx : R.val≤positiveSubspace K (s+3) :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr (hvx ▸ hx)
    rw [hfixP R hRx]
    change Submodule.span K {v}=Submodule.span K {CFSGOrthogonalBNegativeDilation.map K (s+3) t v}
    rw [hemap,hy0,smul_zero,add_zero,←hvx]
  have hxy : B y x=0 := by
    have hxx : B x x=0 := positiveSubspace_singular K (s+3) x hx x hx
    have hyy : B y y=0 := (negativeSingular K (s+3)).property y hy y hy
    have hsym : B x y=B y x := gram_pairing_symmetric (s+3) x y
    have heB : B (x+y) (x+y)=0 := he ▸ hv
    simp only [map_add,LinearMap.add_apply,hxx,hyy,hsym,
      zero_add,add_zero] at heB
    have ht2 : (2 : K)*B y x=0 := by simpa only [two_mul] using heB
    exact (mul_eq_zero.mp ht2).resolve_left h2
  have hsum0 : x+y≠0 := fun h=>hv0 (he.trans h)
  have hsum : B (x+y) (x+y)=0 := he ▸ hv
  have hr : ray B (x+y) hsum0 hsum=R := by
    apply Subtype.ext
    exact congrArg (fun z=>Submodule.span K {z}) he.symm
  have h := htr x y hx hx0 hy hy0 hxy hsum0 hsum
  rw [hr] at h
  rw [hemap]
  exact h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleDilation
