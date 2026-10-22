import SymmetricSubgroupAsymptotics.CFSGOrthogonalBStarVectorAvoidance
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneIntersectionPartition
import SymmetricSubgroupAsymptotics.CFSGSingularPairSpan

/-! Actual local bridge on the original B singular-plane star: any three
planes through an original singular point admit a fourth that meets each
in that point with nonsingular sum. This discharges the local bridge
required for point reconstruction, without an Out or recognition input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
open CFSGOrthogonalBIntrinsicLongRoots CFSGTwoDimensionalSubmoduleBasis
open CFSGOrthogonalBStarVectorAvoidance CFSGSingularPairSpan
variable {K : Type} [Field K] [Finite K]

theorem exists_star_bridge (h2 : (2 : K) ≠ 0) (s : ℕ)
    (u : Index (s+3) → K) (hu : u≠0)
    (P Q T : SingularPlanes (K:=K) s) (huP : u∈P.val) (huQ : u∈Q.val) (huT : u∈T.val) :
    ∃ R : SingularPlanes (K:=K) s,u∈R.val ∧ IntersectingNonadjacent s P R ∧
      IntersectingNonadjacent s Q R ∧ IntersectingNonadjacent s T R := by
  classical
  obtain ⟨v₁,hv₁,i₁,_⟩ := exists_companion P.val P.property.1 u huP hu
  obtain ⟨v₂,hv₂,i₂,_⟩ := exists_companion Q.val Q.property.1 u huQ hu
  obtain ⟨v₃,hv₃,i₃,_⟩ := exists_companion T.val T.property.1 u huT hu
  obtain ⟨w,_,zw,pu,a₁,a₂,a₃⟩ := exists_avoiding_at_axis K h2 s u v₁ v₂ v₃ hu
    (P.property.2 u huP u huP) (P.property.2 v₁ hv₁ v₁ hv₁)
    (Q.property.2 v₂ hv₂ v₂ hv₂) (T.property.2 v₃ hv₃ v₃ hv₃)
    (P.property.2 u huP v₁ hv₁) (Q.property.2 u huQ v₂ hv₂)
    (T.property.2 u huT v₃ hv₃) i₁ i₂ i₃
  have hi : ∀c:K,w≠c•u := by
    intro c hc
    apply a₁
    rw [hc,map_smul]
    rw [gram_pairing_symmetric (s+3) v₁ u,P.property.2 u huP v₁ hv₁,smul_zero]
  have hwu : (gram K (s+3)).toBilin' w u=0 :=
    (gram_pairing_symmetric (s+3) w u).trans pu
  let R : SingularPlanes (K:=K) s := ⟨Submodule.span K {u,w},
    finrank_pair u w hu hi,zeroOn_pair (gram K (s+3)).toBilin' u w
      (P.property.2 u huP u huP) pu hwu zw⟩
  have huR : u∈R.val := Submodule.subset_span (by simp)
  have hwR : w∈R.val := Submodule.subset_span (by simp)
  have hrel : ∀ (A : SingularPlanes (K:=K) s) (v : Index (s+3) → K),
      u∈A.val → v∈A.val → (gram K (s+3)).toBilin' v w≠0 →
        IntersectingNonadjacent s A R := by
    intro A v huA hvA ha
    have hne : A.val≠R.val := by
      intro he
      exact ha (A.property.2 v hvA w (he.symm ▸ hwR))
    have hd : ¬Disjoint A.val R.val := by
      intro h
      have hz : u∈(⊥ : Submodule K (Index (s+3) → K)) :=
        (disjoint_iff.mp h) ▸ (show u∈A.val⊓R.val from ⟨huA,huR⟩)
      exact hu (by simpa only [Submodule.mem_bot] using hz)
    refine ⟨CFSGTwoPlaneIntersectionPartition.inf_finrank_eq_one_of_not_disjoint
      A.val R.val A.property.1 R.property.1 hne hd,?_⟩
    intro hs
    exact ha (hs v (Submodule.mem_sup_left hvA) w (Submodule.mem_sup_right hwR))
  exact ⟨R,huR,hrel P v₁ huP hv₁ a₁,hrel Q v₂ huQ hv₂ a₂,hrel T v₃ huT hv₃ a₃⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
