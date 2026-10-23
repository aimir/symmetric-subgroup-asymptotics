import SymmetricSubgroupAsymptotics.PermutationCycleCoboundary
import SymmetricSubgroupAsymptotics.PermutationalWreathProduct

/-! Actual base conjugacy for EVERY finite top permutation. The complete
set of products on its actual cycles classifies base conjugacy, retaining
all cycles and every base coordinate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.PermutationWreathBaseConjugacy
open PermutationCycleDecomposition PermutationCycleCoboundary
variable {D I : Type*} [CommGroup D] [Finite I]

abbrev Wreath (D I : Type*) [Group D] :=
  PermutationalWreathProduct D (Equiv.Perm I) I

def element (σ : Equiv.Perm I) (f : I → D) : Wreath D I := ⟨f,σ⁻¹⟩

def baseElement (v : I → D) : Wreath D I := ⟨v,1⟩

omit [Finite I] in
theorem base_conjugate_left (σ : Equiv.Perm I) (v f : I → D) (i : I) :
    (baseElement v * element σ f * (baseElement v)⁻¹).left i=
      v i*f i*(v (σ i))⁻¹ := by
  simp [baseElement,element,PermutationalWreathProduct.mul_left,
    PermutationalWreathProduct.mul_right,PermutationalWreathProduct.inv_left]

omit [Finite I] in
theorem base_conjugate_eq_iff (σ : Equiv.Perm I) (v f g : I → D) :
    baseElement v * element σ f * (baseElement v)⁻¹=element σ g ↔
      ∀i,g i=v i*f i*(v (σ i))⁻¹ := by
  constructor
  · intro he i
    have hi := congrArg (fun w : Wreath D I => w.left i) he
    dsimp only at hi
    rw [base_conjugate_left] at hi
    exact hi.symm
  · intro he
    apply PermutationalWreathProduct.ext
    · funext i
      exact (base_conjugate_left σ v f i).trans (he i).symm
    · simp [baseElement,element,PermutationalWreathProduct.mul_right,
        PermutationalWreathProduct.inv_right]

theorem cycleProducts_eq_iff_exists_gauge (σ : Equiv.Perm I) (f g : I → D) :
    (∀c,cycleProduct σ f c=cycleProduct σ g c) ↔
      ∃v : I → D,∀i,g i=v i*f i*(v (σ i))⁻¹ := by
  constructor
  · intro hprod
    have hr : ∀c,cycleProduct σ (fun i => f i*(g i)⁻¹) c=1 := by
      intro c
      change (∏j : Fin (cycleLength σ c),
        f (pointChart σ ⟨c,j⟩)*(g (pointChart σ ⟨c,j⟩))⁻¹)=1
      rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
      change cycleProduct σ f c*(cycleProduct σ g c)⁻¹=1
      rw [hprod c,mul_inv_cancel]
    obtain ⟨v,hv⟩ := exists_global_coboundary σ (fun i => f i*(g i)⁻¹) hr
    refine ⟨v,fun i => ?_⟩
    have hi := congrArg (fun t : D => v i*t*g i*(v (σ i))⁻¹) (hv i)
    simpa [mul_assoc,mul_comm,mul_left_comm] using hi.symm
  · rintro ⟨v,hv⟩ c
    have hr : ∀i,f i*(g i)⁻¹=(v i)⁻¹*v (σ i) := by
      intro i
      rw [hv i]
      simp [mul_assoc,mul_comm,mul_left_comm]
    have hc := ((all_cycleProducts_one_iff σ (fun i => f i*(g i)⁻¹)).mpr ⟨v,hr⟩) c
    change (∏j : Fin (cycleLength σ c),
      f (pointChart σ ⟨c,j⟩)*(g (pointChart σ ⟨c,j⟩))⁻¹)=1 at hc
    rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib] at hc
    exact mul_inv_eq_one.mp hc

theorem cycleProducts_eq_iff_base_conjugate (σ : Equiv.Perm I) (f g : I → D) :
    (∀c,cycleProduct σ f c=cycleProduct σ g c) ↔
      ∃v : I → D,
        baseElement v * element σ f * (baseElement v)⁻¹=element σ g := by
  simp only [base_conjugate_eq_iff]
  exact cycleProducts_eq_iff_exists_gauge σ f g

end SymmetricSubgroupAsymptotics.PermutationWreathBaseConjugacy
