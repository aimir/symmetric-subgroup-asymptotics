import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSemilinearPolarSimilitude
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDLinearSimilitudeCoordinates
import Mathlib.SetTheory.Cardinal.Finite

/-! The actual original D automorphisms in rank at least five inject into
the field factor times the ACTUAL singular-point image of GO. The proven
scalar-kernel containment bounds that image by the isometry group. No
chosen representative is assumed unique, and no quotient automorphism
is lifted arbitrarily to the original matrix group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDAutomorphismCardinality
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGOrthogonalDFieldGeometry
open CFSGOrthogonalDIndexPlaneFamilyAction CFSGOrthogonalDSemilinearPolarSimilitude
open CFSGOrthogonalDProjectiveSimilitudes CFSGOrthogonalDLinearSimilitudeCoordinates
open CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K] [Finite K]

theorem exists_field_pointImage (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (F : MulAut (elementaryProjective K (s+5))) :
    ∃(σ : K≃+*K) (R : (pointHom K (s+5)).range),
      normalizedPoints (s+5) (originalPointPermutationHom K p s F) σ=R.val := by
  obtain ⟨σ,c,L,hc,hQ,hL⟩ := original_field_similitude_decomposition K p s F
  let g := ofLinearEquiv K (s+5) L c hc hQ
  have he : normalizedPoints (s+5) (originalPointPermutationHom K p s F) σ=
      pointHom K (s+5) g := by
    rw [ofLinearEquiv_point]
    apply Equiv.ext
    intro R
    apply Subtype.ext
    exact hL R
  exact ⟨σ,⟨pointHom K (s+5) g,⟨g,rfl⟩⟩,he⟩

theorem automorphism_card_le_pointImage_mul_field (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) [IsSimpleGroup (elementaryProjective K (s+5))] :
    Nat.card (MulAut (elementaryProjective K (s+5)))≤
      Nat.card (pointHom K (s+5)).range*Nat.card (K≃+*K) := by
  classical
  choose σ R hR using exists_field_pointImage K p s
  let code (F : MulAut (elementaryProjective K (s+5))) := (σ F,R F)
  have hinj : Function.Injective code := by
    intro F G he
    have hσ : σ F=σ G := congrArg Prod.fst he
    have hRG : R F=R G := congrArg Prod.snd he
    have hh : normalizedPoints (s+5) (originalPointPermutationHom K p s F) (σ F)=
        normalizedPoints (s+5) (originalPointPermutationHom K p s G) (σ F) := by
      rw [hR F,hRG,←hR G,hσ]
    apply originalPointAction_injective K p s
    apply Subtype.ext
    apply Equiv.ext
    intro P
    apply (CFSGOrthogonalDFieldGeometry.pointEquiv (σ F).symm (s+5)).injective
    exact congrArg (fun e : Equiv.Perm (Points (splitQuadraticForm K (s+5)))=>e P) hh
  letI : Finite (K≃+*K) := Finite.of_injective
    (fun τ : K≃+*K=>(τ : K→K)) DFunLike.coe_injective
  have h := Nat.card_le_card_of_injective code hinj
  simpa only [Nat.card_prod,mul_comm] using h

theorem automorphism_card_le_quadratic_mul_field (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) [IsSimpleGroup (elementaryProjective K (s+5))] :
    Nat.card (MulAut (elementaryProjective K (s+5)))≤
      Nat.card (quadraticPreserving K (s+5))*Nat.card (K≃+*K) :=
  (automorphism_card_le_pointImage_mul_field K p s).trans
    (Nat.mul_le_mul_right _ (pointImage_card_le_quadratic K (s+5) (by omega)))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDAutomorphismCardinality
