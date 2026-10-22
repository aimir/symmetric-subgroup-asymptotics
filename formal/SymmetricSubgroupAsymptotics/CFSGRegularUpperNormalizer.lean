import SymmetricSubgroupAsymptotics.CFSGRegularUpperFlagRecovery

/-! A unitriangular subgroup containing one regular upper element has
its complete coordinate flag intrinsically determined. Its full
normalizer is triangular over every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGRegularUpperNormalizer
open CFSGMatrixFlagNormalizer
variable {K G : Type*} [Field K] [Group G] {m : ℕ}
    (ρ : G→*Matrix (Fin (m+1)) (Fin (m+1)) K) (U : Subgroup G)
    (hupper : ∀u∈U,(ρ u).BlockTriangular id)
    (hdiag : ∀u∈U,∀i,ρ u i i=1)
    (hregular : ∃u∈U,∀i : Fin m,ρ u i.castSucc i.succ≠0)

include hupper hdiag hregular

theorem mem_prefix_succ_iff (k : ℕ) (v : Fin (m+1)→K) :
    v∈flagPrefix (K:=K) (Equiv.refl _) (k+1) ↔
      ∀u∈U,ρ u*ᵥv-v∈flagPrefix (K:=K) (Equiv.refl _) k := by
  constructor
  · intro hv u hu i hi
    have he : (ρ u*ᵥv) i=v i := by
      change (∑j,ρ u i j*v j)=v i
      calc
        _=ρ u i i*v i := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            rcases lt_or_gt_of_ne hji with hj|hj
            · rw [hupper u hu hj,zero_mul]
            · have hz : v j=0 := hv j (by
                change k ≤ i.val at hi
                change i.val<j.val at hj
                change k+1≤j.val
                omega)
              rw [hz,mul_zero]
          · intro hn
            exact False.elim (hn (Finset.mem_univ i))
        _=v i := by rw [hdiag u hu i,one_mul]
    change (ρ u*ᵥv) i-v i=0
    rw [he,sub_self]
  · intro hv
    obtain ⟨u,hu,hreg⟩ := hregular
    exact CFSGRegularUpperFlagRecovery.recover_prefix (ρ u) (hupper u hu) (hdiag u hu)
      hreg k v (hv u hu)

theorem normalizer_preserves_prefix (a : G)
    (ha : a∈Subgroup.normalizer (U : Set G)) :
    ∀k (v : Fin (m+1)→K),v∈flagPrefix (K:=K) (Equiv.refl _) k→
      ρ a*ᵥv∈flagPrefix (K:=K) (Equiv.refl _) k := by
  intro k
  induction k with
  | zero =>
    intro v hv
    have hz : v=0 := funext fun i=>hv i (Nat.zero_le _)
    rw [hz,Matrix.mulVec_zero]
    exact (flagPrefix (K:=K) (Equiv.refl _) 0).zero_mem
  | succ k ih =>
    intro v hv
    apply (mem_prefix_succ_iff ρ U hupper hdiag hregular k _).mpr
    intro u hu
    have hc : a⁻¹*u*a∈U := (Subgroup.mem_normalizer_iff''.mp ha u).mp hu
    have hd := (mem_prefix_succ_iff ρ U hupper hdiag hregular k v).mp hv (a⁻¹*u*a) hc
    have h := ih (ρ (a⁻¹*u*a)*ᵥv-v) hd
    have he : a*(a⁻¹*u*a)=u*a := by group
    have hact : ρ a*ᵥ(ρ (a⁻¹*u*a)*ᵥv)=ρ u*ᵥ(ρ a*ᵥv) := by
      rw [Matrix.mulVec_mulVec,←map_mul,he,map_mul,←Matrix.mulVec_mulVec]
    simpa only [Matrix.mulVec_sub,hact] using h

theorem normalizer_upper (a : G) (ha : a∈Subgroup.normalizer (U : Set G)) :
    (ρ a).BlockTriangular id := by
  intro i j hij
  have hv : Pi.single j (1:K)∈flagPrefix (K:=K) (Equiv.refl _) (j.val+1) := by
    intro l hl
    have hlj : l≠j := by intro he; subst l; change j.val+1≤j.val at hl; omega
    exact Pi.single_eq_of_ne hlj 1
  have h := normalizer_preserves_prefix ρ U hupper hdiag hregular a ha
    (j.val+1) (Pi.single j 1) hv i (by change j.val < i.val at hij; exact hij)
  change (ρ a*ᵥPi.single j 1) i=0 at h
  rwa [Matrix.mulVec_single_one] at h

end SymmetricSubgroupAsymptotics.CFSGRegularUpperNormalizer
