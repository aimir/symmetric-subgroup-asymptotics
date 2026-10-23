import SymmetricSubgroupAsymptotics.PermutationCycleDecomposition
import SymmetricSubgroupAsymptotics.CyclicCoordinateCoboundary

/-! Global cyclic coboundaries on an arbitrary finite permutation set.
All actual cycle products are one exactly when one global potential
realizes the labeling. The actual SameCycle quotient retains all cycles. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.PermutationCycleCoboundary
open PermutationCycleDecomposition
variable {D I : Type*} [CommGroup D] [Finite I]

theorem product_coboundary_any_length (m : ℕ) (v : Fin m → D) :
    (∏i,(v i)⁻¹*v (finRotate m i))=1 := by
  rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,
    Equiv.prod_comp (finRotate m) v,inv_mul_cancel]

theorem exists_coboundary_any_length (m : ℕ) (f : Fin m → D)
    (hf : (∏i,f i)=1) :
    ∃v : Fin m → D,∀i,f i=(v i)⁻¹*v (finRotate m i) := by
  cases m with
  | zero => exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n => exact CyclicCoordinateCoboundary.exists_coboundary_of_product_one f hf

def cycleProduct (σ : Equiv.Perm I) (f : I → D) (c : CycleIndex σ) : D :=
  ∏j : Fin (cycleLength σ c),f (pointChart σ ⟨c,j⟩)

theorem exists_global_coboundary (σ : Equiv.Perm I) (f : I → D)
    (hf : ∀c,cycleProduct σ f c=1) :
    ∃v : I → D,∀i,f i=(v i)⁻¹*v (σ i) := by
  have hlocal : ∀c : CycleIndex σ,∃v : Fin (cycleLength σ c) → D,
      ∀j,f (pointChart σ ⟨c,j⟩)=(v j)⁻¹*v (finRotate _ j) := by
    intro c
    exact exists_coboundary_any_length _ _ (hf c)
  let v : ∀c : CycleIndex σ,Fin (cycleLength σ c) → D :=
    fun c => Classical.choose (hlocal c)
  have hv (c : CycleIndex σ) := Classical.choose_spec (hlocal c)
  refine ⟨fun i => v ((pointChart σ).symm i).1 ((pointChart σ).symm i).2,?_⟩
  intro i
  obtain ⟨⟨c,j⟩,rfl⟩ := (pointChart σ).surjective i
  dsimp only
  rw [← pointChart_rotate,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact hv c j

theorem cycleProduct_global_coboundary (σ : Equiv.Perm I) (v : I → D)
    (c : CycleIndex σ) :
    cycleProduct σ (fun i => (v i)⁻¹*v (σ i)) c=1 := by
  change (∏j : Fin (cycleLength σ c),
    (v (pointChart σ ⟨c,j⟩))⁻¹*v (σ (pointChart σ ⟨c,j⟩)))=1
  simp_rw [← pointChart_rotate]
  exact product_coboundary_any_length _ (fun j => v (pointChart σ ⟨c,j⟩))

theorem all_cycleProducts_one_iff (σ : Equiv.Perm I) (f : I → D) :
    (∀c,cycleProduct σ f c=1) ↔ ∃v : I → D,∀i,f i=(v i)⁻¹*v (σ i) := by
  constructor
  · exact exists_global_coboundary σ f
  · rintro ⟨v,hv⟩ c
    have he : f=(fun i => (v i)⁻¹*v (σ i)) := funext hv
    rw [he]
    exact cycleProduct_global_coboundary σ v c

end SymmetricSubgroupAsymptotics.PermutationCycleCoboundary
