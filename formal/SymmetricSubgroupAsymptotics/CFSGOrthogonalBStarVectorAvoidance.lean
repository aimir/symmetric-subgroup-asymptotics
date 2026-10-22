import SymmetricSubgroupAsymptotics.CFSGOrthogonalBThreeTangents
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootProductOrthogonality
import Mathlib.Tactic.LinearCombination

/-! At an actual original singular point, three actual singular-plane
directions admit one further singular direction nonorthogonal to all
three. The tail is the SAME smaller original B space, including its
middle coordinate; no polar-space recognition premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBStarVectorAvoidance
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBTailCoordinates
open CFSGOrthogonalBVectorCoordinates CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSingularVectorCount CFSGOrthogonalBIntrinsicLongRoots
variable (K : Type) [Field K] [Finite K]

theorem pairing_tail_of_negative_heads_zero (h2 : (2 : K) ≠ 0) (n : ℕ)
    (v w : Index (n+1) → K) (hv : v (neg (n+1) 0)=0) (hw : w (neg (n+1) 0)=0) :
    (gram K (n+1)).toBilin' v w =
      (gram K n).toBilin' (tailRestriction K n v) (tailRestriction K n w) := by
  have ht : tailRestriction K n (v+w)=tailRestriction K n v+tailRestriction K n w := rfl
  have hsum := gram_norm_tail_of_negative_head_zero K n (v+w) (by simp [hv,hw])
  have hnormv := gram_norm_tail_of_negative_head_zero K n v hv
  have hnormw := gram_norm_tail_of_negative_head_zero K n w hw
  rw [ht] at hsum
  simp only [map_add,LinearMap.add_apply] at hsum
  rw [gram_pairing_symmetric (n+1) w v,
    gram_pairing_symmetric n (tailRestriction K n w) (tailRestriction K n v)] at hsum
  apply mul_left_cancel₀ h2
  linear_combination hsum-hnormv-hnormw

theorem exists_avoiding_at_axis (h2 : (2 : K) ≠ 0) (s : ℕ)
    (u v₁ v₂ v₃ : Index (s+3) → K) (hu : u≠0)
    (zu : (gram K (s+3)).toBilin' u u=0)
    (z₁ : (gram K (s+3)).toBilin' v₁ v₁=0)
    (z₂ : (gram K (s+3)).toBilin' v₂ v₂=0)
    (z₃ : (gram K (s+3)).toBilin' v₃ v₃=0)
    (p₁ : (gram K (s+3)).toBilin' u v₁=0)
    (p₂ : (gram K (s+3)).toBilin' u v₂=0)
    (p₃ : (gram K (s+3)).toBilin' u v₃=0)
    (i₁ : ∀ c:K,v₁≠c•u) (i₂ : ∀ c:K,v₂≠c•u) (i₃ : ∀ c:K,v₃≠c•u) :
    ∃ w : Index (s+3) → K,w≠0 ∧ (gram K (s+3)).toBilin' w w=0 ∧
      (gram K (s+3)).toBilin' u w=0 ∧
      (gram K (s+3)).toBilin' v₁ w≠0 ∧ (gram K (s+3)).toBilin' v₂ w≠0 ∧
      (gram K (s+3)).toBilin' v₃ w≠0 := by
  obtain ⟨g,hg⟩ := exists_normalize_singular K h2 (s+1) u hu zu
  let e := naturalLinearEquiv K (s+3) g
  have he : ∀ x y,(gram K (s+3)).toBilin' (e x) (e y)=
      (gram K (s+3)).toBilin' x y := fun x y=>natural_pairing_invariant h2 (s+3) g x y
  have hgu : e u=Pi.single (pos (s+3) 0) 1 := hg
  have hdata : ∀ v : Index (s+3) → K,
      (gram K (s+3)).toBilin' v v=0 → (gram K (s+3)).toBilin' u v=0 →
      (∀ c:K,v≠c•u) →
      (e v) (neg (s+3) 0)=0 ∧ tailRestriction K (s+2) (e v)≠0 ∧
        (gram K (s+2)).toBilin' (tailRestriction K (s+2) (e v))
          (tailRestriction K (s+2) (e v))=0 := by
    intro v zv pv iv
    have hp : (gram K (s+3)).toBilin' (Pi.single (pos (s+3) 0) 1) (e v)=0 := by
      rw [←hgu,he,pv]
    have hn : (e v) (neg (s+3) 0)=0 :=
      (mul_eq_zero.mp ((pairing_first_positive K (s+2) (e v)).symm.trans hp)).resolve_left h2
    refine ⟨hn,?_,?_⟩
    · intro ht
      have hv := vector_eq_first_of_tail_zero K (s+2) (e v) ht hn
      apply iv ((e v) (pos (s+3) 0))
      apply e.injective
      simpa only [map_smul,hgu] using hv
    · exact (gram_norm_tail_of_negative_head_zero K (s+2) (e v) hn).symm.trans
        ((he v v).trans zv)
  obtain ⟨n₁,h₁,t₁⟩ := hdata v₁ z₁ p₁ i₁
  obtain ⟨n₂,h₂,t₂⟩ := hdata v₂ z₂ p₂ i₂
  obtain ⟨n₃,h₃,t₃⟩ := hdata v₃ z₃ p₃ i₃
  obtain ⟨z,hz,zs,a₁,a₂,a₃⟩ := exists_singular_avoiding_three_tangents K h2 s
    (tailRestriction K (s+2) (e v₁)) (tailRestriction K (s+2) (e v₂))
    (tailRestriction K (s+2) (e v₃)) h₁ h₂ h₃ t₁ t₂ t₃
  let w' := cons K (s+2) 0 z
  let w := e.symm w'
  have hew : e w=w' := e.apply_symm_apply w'
  have hns : w' (neg (s+3) 0)=0 := cons_head_negative K (s+2) 0 z
  have hzw : (gram K (s+3)).toBilin' w w=0 := by
    rw [←he w w,hew]
    exact (norm_cons K (s+2) 0 z).trans zs
  have hpu : (gram K (s+3)).toBilin' u w=0 := by
    rw [←he u w,hgu,hew,pairing_first_positive,hns,mul_zero]
  have hpair : ∀ v : Index (s+3) → K,(e v) (neg (s+3) 0)=0 →
      (gram K (s+2)).toBilin' (tailRestriction K (s+2) (e v)) z≠0 →
      (gram K (s+3)).toBilin' v w≠0 := by
    intro v hn hv
    rw [←he v w,hew,pairing_tail_of_negative_heads_zero K h2 (s+2) (e v) w' hn hns]
    simpa only [w',tail_cons] using hv
  have hw₁ := hpair v₁ n₁ a₁
  refine ⟨w,?_,hzw,hpu,hw₁,hpair v₂ n₂ a₂,hpair v₃ n₃ a₃⟩
  intro hzero
  exact hw₁ (by rw [hzero,map_zero])

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBStarVectorAvoidance
