import SymmetricSubgroupAsymptotics.CFSGSuzukiDiagonalTorus
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentGroup
import Mathlib.Tactic.Group

/-! The zero-first-parameter Suzuki Bruhat identity, proved on the
original four-by-four arrays. This is enough to recover every original
torus element from the actual unipotent subgroup and original Weyl
matrix, without assuming a BN-pair or the order of the whole group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiBruhat
open CFSGSuzukiTorus CFSGSuzukiUnipotent CFSGSuzukiFieldParameters
variable {K : Type*} [Field K] [CharP K 2]

def reversingArray : Matrix (Fin 4) (Fin 4) K :=
  !![0,0,0,1;0,0,1,0;0,1,0,0;1,0,0,0]

omit [CharP K 2] in
theorem reversingArray_mul_apply (A : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    ((reversingArray : Matrix (Fin 4) (Fin 4) K)*A) i j=A i.rev j := by
  fin_cases i <;> simp [reversingArray,Matrix.mul_apply,Fin.sum_univ_succ,Fin.rev]

omit [CharP K 2] in
theorem mul_reversingArray_apply (A : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (A*(reversingArray : Matrix (Fin 4) (Fin 4) K)) i j=A i j.rev := by
  fin_cases j <;> simp [reversingArray,Matrix.mul_apply,Fin.sum_univ_succ,Fin.rev]

theorem zero_first_bruhat_array (t : K →+* K) (ht : ∀ x,t (t x)=x^2)
    (b : K) (hb : b≠0) :
    reversingArray*twistedArray t 0 b*reversingArray=
      twistedArray t (b/t b) 0*diagonalTorus t (t b)*reversingArray*
        twistedArray t (b/t b) (1/b) := by
  have htb : t b≠0 := by
    intro he
    apply hb
    apply t.injective
    simpa only [map_zero] using he
  ext i j
  simp only [mul_reversingArray_apply,reversingArray_mul_apply]
  rw [Matrix.mul_apply]
  simp only [mul_reversingArray_apply,diagonalTorus,Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [twistedArray,Fin.sum_univ_succ,map_div₀,ht,Fin.rev] <;>
    field_simp [hb,htb] <;> ring_nf <;> simp

theorem zero_first_bruhat (m : ℕ) (b : Field m) (hb : b≠0) :
    weylElement m*unipotentElement m 0 b*weylElement m=
      unipotentElement m (b/theta m b) 0*
        normalizedTorusElement m (Units.mk0 (theta m b) (theta_ne_zero m hb))*weylElement m*
        unipotentElement m (b/theta m b) (1/b) := by
  apply Units.ext
  change CFSG.Models.SuzukiConstruction.weyl m*
      CFSG.Models.SuzukiConstruction.unipotent m 0 b*CFSG.Models.SuzukiConstruction.weyl m=
    CFSG.Models.SuzukiConstruction.unipotent m (b/theta m b) 0*
      (normalizedTorusElement m (Units.mk0 (theta m b) (theta_ne_zero m hb)) :
        CFSG.Models.SuzukiConstruction.Mat m)*CFSG.Models.SuzukiConstruction.weyl m*
      CFSG.Models.SuzukiConstruction.unipotent m (b/theta m b) (1/b)
  rw [normalizedTorusElement_coe]
  simp only [unipotent_eq_twistedArray]
  exact zero_first_bruhat_array (theta m) (theta_twice m) b hb

/-- Every actual normalized torus lies in any subgroup containing the
original U and W. No two-generator or Sylow assumption occurs. -/
theorem normalizedTorus_mem_of_unipotent_weyl (m : ℕ)
    (H : Subgroup (CFSGSuzukiTorus.Ambient m))
    (hU : unipotentSubgroup m≤H) (hW : weylElement m∈H) (c : (Field m)ˣ) :
    normalizedTorusElement m c∈H := by
  let b : Field m := inverseTheta m (c : Field m)
  have hb : b≠0 := by
    intro he
    apply Units.ne_zero c
    apply (inverseTheta m).injective
    simpa only [b,map_zero] using he
  have hc : Units.mk0 (theta m b) (theta_ne_zero m hb)=c := by
    apply Units.ext
    exact theta_inverseTheta m (c : Field m)
  have he := zero_first_bruhat m b hb
  rw [hc] at he
  have hleft : unipotentElement m (b/theta m b) 0∈H := hU ⟨_,_,rfl⟩
  have hright : unipotentElement m (b/theta m b) (1/b)∈H := hU ⟨_,_,rfl⟩
  have hmid : unipotentElement m (b/theta m b) 0*normalizedTorusElement m c*
      weylElement m*unipotentElement m (b/theta m b) (1/b)∈H := by
    rw [←he]
    exact H.mul_mem (H.mul_mem hW (hU ⟨0,b,rfl⟩)) hW
  have hresult := H.mul_mem
    (H.mul_mem (H.mul_mem (H.inv_mem hleft) hmid) (H.inv_mem hright)) (H.inv_mem hW)
  have hcancel :
      ((unipotentElement m (b/theta m b) 0)⁻¹*
        (unipotentElement m (b/theta m b) 0*normalizedTorusElement m c*
          weylElement m*unipotentElement m (b/theta m b) (1/b)))*
        (unipotentElement m (b/theta m b) (1/b))⁻¹*(weylElement m)⁻¹=
        normalizedTorusElement m c := by group
  rw [hcancel] at hresult
  exact hresult

theorem torus_mem_of_unipotent_weyl (m : ℕ)
    (H : Subgroup (CFSGSuzukiTorus.Ambient m))
    (hU : unipotentSubgroup m≤H) (hW : weylElement m∈H) (c : (Field m)ˣ) :
    torusElement m c∈H := by
  have hy : torusParameter m (c : Field m)≠0 :=
    mul_ne_zero (Units.ne_zero c) (by
      intro he
      apply Units.ne_zero c
      apply (inverseTheta m).injective
      simpa only [map_zero] using he)
  let d : (Field m)ˣ := Units.mk0 (torusParameter m (c : Field m)) hy
  have he : normalizedTorusElement m d=torusElement m c := by
    apply Units.ext
    rw [normalizedTorusElement_coe,torusElement_coe,original_torus_eq_diagonalTorus]
    rfl
  rw [←he]
  exact normalizedTorus_mem_of_unipotent_weyl m H hU hW d

/-- The original model is already generated by actual U and actual W;
all original torus parameters have been recovered by the checked word. -/
theorem model_le_of_unipotent_weyl (m : ℕ)
    (H : Subgroup (CFSGSuzukiTorus.Ambient m))
    (hU : unipotentSubgroup m≤H) (hW : weylElement m∈H) :
    CFSG.Models.SuzukiConstruction.subgroup m≤H := by
  apply (Subgroup.closure_le H).mpr
  intro g hg
  rcases hg with ⟨a,b,hg⟩|⟨c,hg⟩|hg
  · have he : g=unipotentElement m a b := Units.ext hg
    rw [he]
    exact hU ⟨a,b,rfl⟩
  · have he : g=torusElement m c := Units.ext hg
    rw [he]
    exact torus_mem_of_unipotent_weyl m H hU hW c
  · have he : g=weylElement m := Units.ext hg
    rw [he]
    exact hW

end SymmetricSubgroupAsymptotics.CFSGSuzukiBruhat
