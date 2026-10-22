import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularSubspaceTail
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveSubspace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneOrbit
import SymmetricSubgroupAsymptotics.CFSGSingularSubspaceIsometry

/-! Actual root words carry every full-rank original singular B
subspace to the literal positive subspace. Rank one uses genuine scaled
normalization, and the induction retains the SAME tail and its kernel. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBMaximalSubspaceOrbit
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSingularVectorCount CFSGOrthogonalBTailCoordinates
open CFSGOrthogonalBSingularSubspaceTail CFSGOrthogonalBPositiveSubspace CFSGPolarSubspacePoints
variable (K : Type) [Field K] [Finite K]

omit [Finite K] in
theorem exists_scaled_normalize (h2 : (2 : K) ≠ 0) (n : ℕ)
    (v : Index (n+1) → K) (hv : v≠0) (hz : (gram K (n+1)).toBilin' v v=0) :
    ∃g : elementaryRootGroup K (n+1),∃a : K,a≠0 ∧
      (g.val : Mat K (n+1))*ᵥv=a•Pi.single (pos (n+1) 0) 1 := by
  cases n with
  | zero => exact CFSGOrthogonalBIsometryIndexRankOneOrbit.exists_scalar_normalize K h2 v hv hz
  | succ n =>
    obtain ⟨g,hg⟩ := exists_normalize_singular K h2 n v hv hz
    exact ⟨g,1,one_ne_zero,by simpa only [one_smul] using hg⟩

def naturalSubspace (h2 : (2 : K) ≠ 0) (n : ℕ) (g : elementaryRootGroup K n)
    (P : Subspaces (gram K n).toBilin') : Subspaces (gram K n).toBilin' :=
  isometrySubspace (gram K n).toBilin' (naturalLinearEquiv K n g)
    (fun x y=>natural_pairing_invariant h2 n g x y) P

omit [Finite K] in
theorem naturalSubspace_finrank (h2 : (2 : K) ≠ 0) (n : ℕ)
    (g : elementaryRootGroup K n) (P : Subspaces (gram K n).toBilin') :
    Module.finrank K (naturalSubspace K h2 n g P).val=Module.finrank K P.val :=
  isometrySubspace_finrank (gram K n).toBilin' (naturalLinearEquiv K n g)
    (fun x y=>natural_pairing_invariant h2 n g x y) P

theorem exists_normalize_full_rank (h2 : (2 : K) ≠ 0) (n : ℕ)
    (P : Subspaces (gram K n).toBilin') (hd : Module.finrank K P.val=n) :
    ∃g : elementaryRootGroup K n,P.val.map (Matrix.mulVecLin (g.val : Mat K n))=
      positiveSubspace K n := by
  induction n with
  | zero =>
    have hP : P.val=⊥ := Submodule.finrank_eq_zero.mp hd
    have hQ : positiveSubspace K 0=⊥ := Submodule.finrank_eq_zero.mp (positiveSubspace_finrank K 0)
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,Units.val_one,Matrix.mulVecLin_one,Submodule.map_id,hP,hQ]
  | succ n ih =>
    obtain ⟨u,hu,hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p:=P.val)
      (Submodule.one_le_finrank_iff.mp (by rw [hd];omega))
    obtain ⟨g,a,ha,hg⟩ := exists_scaled_normalize K h2 n u hu0 (P.property u hu u hu)
    let P₀ := naturalSubspace K h2 (n+1) g P
    have hP₀ : Module.finrank K P₀.val=n+1 := (naturalSubspace_finrank K h2 (n+1) g P).trans hd
    have hgu : (g.val : Mat K (n+1))*ᵥu∈P₀.val := ⟨u,hu,rfl⟩
    have he₀ : Pi.single (pos (n+1) 0) 1∈P₀.val := by
      have hm := P₀.val.smul_mem a⁻¹ hgu
      rw [hg,smul_smul,inv_mul_cancel₀ ha,one_smul] at hm
      exact hm
    let T := tailSubspace K h2 n P₀ he₀
    have hT : Module.finrank K T.val=n := by
      have h := tailSubspace_finrank K h2 n P₀ he₀
      change Module.finrank K T.val+1=Module.finrank K P₀.val at h
      rw [hP₀] at h
      omega
    obtain ⟨h,hh⟩ := ih T hT
    let t := tailElementaryHom K n h
    let P₁ := naturalSubspace K h2 (n+1) t P₀
    have hP₁ : Module.finrank K P₁.val=n+1 := (naturalSubspace_finrank K h2 (n+1) t P₀).trans hP₀
    have hle : P₁.val ≤ positiveSubspace K (n+1) := by
      rintro v ⟨x,hx,rfl⟩
      apply mem_positiveSubspace_of_tail K n
      · change (((tailElementaryHom K n h).val : Mat K (n+1))*ᵥx) (neg (n+1) 0)=0
        rw [tailElementaryHom_head_negative]
        exact negative_head_zero K h2 n P₀ he₀ x hx
      · change tailRestriction K n (((tailElementaryHom K n h).val : Mat K (n+1))*ᵥx)∈_
        rw [tailElementaryHom_tail_action]
        have hm : (h.val : Mat K n)*ᵥtailRestriction K n x∈
            T.val.map (Matrix.mulVecLin (h.val : Mat K n)) :=
          ⟨tailRestriction K n x,⟨x,hx,rfl⟩,rfl⟩
        rw [hh] at hm
        exact hm
    have heq : P₁.val=positiveSubspace K (n+1) := Submodule.eq_of_le_of_finrank_le hle
      (by rw [positiveSubspace_finrank,hP₁])
    refine ⟨t*g,?_⟩
    calc
      P.val.map (Matrix.mulVecLin ((t*g).val : Mat K (n+1)))=
          (P.val.map (Matrix.mulVecLin (g.val : Mat K (n+1)))).map
            (Matrix.mulVecLin (t.val : Mat K (n+1))) := by
        change P.val.map (Matrix.mulVecLin ((t.val : Mat K (n+1))*(g.val : Mat K (n+1))))=_
        rw [Matrix.mulVecLin_mul,Submodule.map_comp]
      _=positiveSubspace K (n+1) := heq

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBMaximalSubspaceOrbit
