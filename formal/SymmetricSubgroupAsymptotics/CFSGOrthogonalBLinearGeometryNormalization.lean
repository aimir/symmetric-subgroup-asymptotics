import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSpecialGeometry
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedPairAlignment
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositivePointNormalization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPairedNondegeneracy
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedCommonRatio
import SymmetricSubgroupAsymptotics.CFSGPolarLinearPieceRange
import SymmetricSubgroupAsymptotics.CFSGPolarOpposedPointFixation
import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceOpposition

/-! Actual special isometries normalize any locally linear original B
polar map to pointwise fixation of BOTH opposed coordinate spaces.
The range of its positive representative and the opposite-point
fixation are derived internally from the actual point incidence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBLinearGeometryNormalization
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBOpposedGraphShear CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBPositivePointNormalization CFSGOrthogonalBOpposedPairAlignment
open CFSGOrthogonalBPairedNondegeneracy CFSGOrthogonalBOpposedCommonRatio
open CFSGPolarSubspacePoints CFSGSingularPlaneTriangle CFSGOrthogonalBIntrinsicLongRoots
variable (K : Type) [Field K] [Finite K]
local instance (σ : K≃+*K) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ
local instance (σ : K≃+*K) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

theorem exists_opposed_point_normalization (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K)≠0) (s : ℕ)
    (f : Points (gram K (s+3)).toBilin'≃Points (gram K (s+3)).toBilin')
    (l : Planes (gram K (s+3)).toBilin'≃Planes (gram K (s+3)).toBilin')
    (hinc : ∀P L,(f P).val≤(l L).val ↔ P.val≤L.val)
    (horth : ∀P Q,ZeroOn (gram K (s+3)).toBilin' (f P).val (f Q).val ↔
      ZeroOn (gram K (s+3)).toBilin' P.val Q.val)
    (hlinear : ∀W : Subspaces (gram K (s+3)).toBilin',Module.finrank K W.val=s+3 →
      Nonempty (SemilinearPiece (gram K (s+3)).toBilin' f W (RingEquiv.refl K))) :
    ∃a : specialFormUnits K (s+3),
      (∀R : Points (gram K (s+3)).toBilin',R.val≤positiveSubspace K (s+3) →
        CFSGOrthogonalBSpecialGeometry.point K (s+3) a (f R)=R) ∧
      (∀R : Points (gram K (s+3)).toBilin',R.val≤negativeSubspace K (s+3) →
        CFSGOrthogonalBSpecialGeometry.point K (s+3) a (f R)=R) := by
  let B := (gram K (s+3)).toBilin'
  let P : Subspaces B := ⟨positiveSubspace K (s+3),positiveSubspace_singular K (s+3)⟩
  let Z := negativeSingular K (s+3)
  let P' := imageSubspace B f l hinc horth P
  let Z' := imageSubspace B f l hinc horth Z
  have hdP : Module.finrank K P.val=s+3 := positiveSubspace_finrank K (s+3)
  have hdZ : Module.finrank K Z.val=s+3 := negative_finrank K (s+3)
  have hdP' : Module.finrank K P'.val=s+3 := (imageSubspace_finrank B f l hinc horth P).trans hdP
  have hdZ' : Module.finrank K Z'.val=s+3 := (imageSubspace_finrank B f l hinc horth Z).trans hdZ
  have hdis : Disjoint P'.val Z'.val := disjoint_iff.mpr
    ((imageSubspace_inf_eq_bot_iff B f l hinc horth P Z).mpr (positive_negative_disjoint K (s+3)).eq_bot)
  obtain ⟨g,hgP,hgZ⟩ := exists_align_opposed_pair K h2 (s+2) P' Z' hdP' hdZ' hdis
  change P'.val.map (g.val : Mat K (s+3)).mulVecLin=P.val at hgP
  change Z'.val.map (g.val : Mat K (s+3)).mulVecLin=Z.val at hgZ
  let gSO : specialFormUnits K (s+3) := ⟨g.val,elementary_le_specialFormUnits K p h2 (s+3) g.property⟩
  let f1 := f.trans (CFSGOrthogonalBSpecialGeometry.point K (s+3) gSO)
  have hP1 : ∀R : Points B,R.val≤P.val → (f1 R).val≤P.val := by
    intro R hR
    change (f R).val.map (g.val : Mat K (s+3)).mulVecLin≤P.val
    rw [←hgP]
    exact Submodule.map_mono ((point_le_image_iff B f l hinc P R).mpr hR)
  have hZ1 : ∀R : Points B,R.val≤Z.val → (f1 R).val≤Z.val := by
    intro R hR
    change (f R).val.map (g.val : Mat K (s+3)).mulVecLin≤Z.val
    rw [←hgZ]
    exact Submodule.map_mono ((point_le_image_iff B f l hinc Z R).mpr hR)
  let F : SemilinearPiece B f1 P (RingEquiv.refl K) :=
    CFSGPolarIsometryGeometry.postcomposePiece B
      (CFSGOrthogonalBSpecialGeometry.linearEquiv K (s+3) gSO)
      (CFSGOrthogonalBSpecialGeometry.pairing K (s+3) gSO)
      f P (RingEquiv.refl K) (Classical.choice (hlinear P hdP))
  let L : P.val→ₗ[K](Index (s+3)→K) := F.map
  have hRange : L.range=P.val := linearPiece_range_eq B f1 P F P.val rfl hP1
  have hrep : ∀R : Points B,∀hR : R.val≤P.val,∀v : Index (s+3)→K,
      ∀hv : v∈R.val,L ⟨v,hR hv⟩∈(f1 R).val := by
    intro R hR v hv
    by_cases hv0 : v=0
    · subst v
      change L 0∈(f1 R).val
      rw [map_zero]
      exact (f1 R).val.zero_mem
    have hvW : (⟨v,hR hv⟩ : P.val)≠0 := fun h=>hv0 (congrArg Subtype.val h)
    have he := F.point ⟨v,hR hv⟩ hvW
    have hr : ray B v hv0 (P.property v (hR hv) v (hR hv))=R :=
      Subtype.ext (point_span B R v hv hv0)
    rw [hr] at he
    exact he ▸ Submodule.mem_span_singleton_self _
  obtain ⟨b,hbP,hbZ⟩ := exists_special_point_normalization K (s+3) L F.injective hRange f1 hrep
  let a := b*gSO
  let f2 := f.trans (CFSGOrthogonalBSpecialGeometry.point K (s+3) a)
  have hfP : ∀R : Points B,R.val≤P.val → f2 R=R := by
    intro R hR
    apply Subtype.ext
    change (f R).val.map ((b.val*gSO.val : (Mat K (s+3))ˣ) : Mat K (s+3)).mulVecLin=R.val
    rw [CFSGMatrixSubspaceUnitAction.map_mul]
    exact hbP R hR
  have hfZ : ∀R : Points B,R.val≤Z.val → (f2 R).val≤Z.val := by
    intro R hR
    change (f R).val.map ((b.val*gSO.val : (Mat K (s+3))ˣ) : Mat K (s+3)).mulVecLin≤Z.val
    rw [CFSGMatrixSubspaceUnitAction.map_mul]
    calc
      _ ≤ Z.val.map (b.val : Mat K (s+3)).mulVecLin := Submodule.map_mono (hZ1 R hR)
      _ = Z.val := hbZ
  have hforth : ∀R S : Points B,ZeroOn B (f2 R).val (f2 S).val ↔ ZeroOn B R.val S.val :=
    fun R S=>(CFSGOrthogonalBSpecialGeometry.orthogonality K (s+3) a (f R) (f S)).trans (horth R S)
  refine ⟨a,hfP,?_⟩
  exact fixes_opposite_of_pairing_nondegenerate B f2 hforth P Z
    (negative_orthogonal_positive_eq_zero K h2 (s+3)) hfP hfZ

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBLinearGeometryNormalization
