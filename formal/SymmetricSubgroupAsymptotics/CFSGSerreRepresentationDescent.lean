import SymmetricSubgroupAsymptotics.CFSGSerreInvariantKernel
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! An actual onto divided-power intertwiner gives a representation of the
original root-generated model on its target. The source action is descended,
not assumed faithful. The actual projective model then maps to the actual
projective image, and simplicity/nontriviality make that map an equivalence. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreRepresentationDescent
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
open CFSGInvariantQuotientAction CFSGSerreInvariantKernel
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]

theorem kernel_stable_of_intertwiners (β : Space A K →ₗ[K] V)
    (D : Bool → Fin n → ℕ → Module.End K V)
    (hD : ∀ negative i k x, β ((integralOperator A negative i k).baseChange K x) =
      D negative i k (β x)) :
    ∀ negative i k x, x ∈ LinearMap.ker β →
      (integralOperator A negative i k).baseChange K x ∈ LinearMap.ker β := by
  intro negative i k x hx
  change β x = 0 at hx
  change β ((integralOperator A negative i k).baseChange K x) = 0
  rw [hD, hx, map_zero]

variable (β : Space A K →ₗ[K] V) (hβ : Function.Surjective β)
    (hker : ∀ negative i k x, x ∈ LinearMap.ker β →
      (integralOperator A negative i k).baseChange K x ∈ LinearMap.ker β)

def modelToStabilizer : Model A K →* stabilizer (LinearMap.ker β) where
  toFun g := ⟨g.val, model_le_stabilizer A K (LinearMap.ker β) hker g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def representation : Model A K →* (V ≃ₗ[K] V) :=
  (descendedAction β hβ).comp (modelToStabilizer A K β hker)

theorem representation_intertwines (g : Model A K) (x : Space A K) :
    representation A K β hβ hker g (β x) = β (g.val x) :=
  descendedAction_intertwines β hβ (modelToStabilizer A K β hker g) x

variable (D : Bool → Fin n → ℕ → Module.End K V)
    (hD : ∀ negative i k x, β ((integralOperator A negative i k).baseChange K x) =
      D negative i k (β x))
include hD

theorem rootOperator_intertwines (negative : Bool) (i : Fin n) (t : K) (x : Space A K) :
    β (rootOperator A K negative i t x) =
      (∑ k ∈ Finset.range 4, t ^ k • D negative i k) (β x) := by
  simp only [rootOperator, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [hD]

theorem representation_root (negative : Bool) (i : Fin n) (t : K) :
    (representation A K β hβ hker
      ⟨rootEquiv A K negative i t, rootEquiv_mem_model A K negative i t⟩).toLinearMap =
        ∑ k ∈ Finset.range 4, t ^ k • D negative i k := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hβ y
  change representation A K β hβ hker
    ⟨rootEquiv A K negative i t, rootEquiv_mem_model A K negative i t⟩ (β x) =
      (∑ k ∈ Finset.range 4, t ^ k • D negative i k) (β x)
  rw [representation_intertwines]
  exact rootOperator_intertwines A K β D hD negative i t x

omit D hD in
def imageModel : Subgroup (V ≃ₗ[K] V) := (representation A K β hβ hker).range

omit D hD in
def projectiveEquivToImage [IsSimpleGroup (Projective A K)]
    [Nontrivial (imageModel A K β hβ hker ⧸ Subgroup.center (imageModel A K β hβ hker))] :
    Projective A K ≃*
      imageModel A K β hβ hker ⧸ Subgroup.center (imageModel A K β hβ hker) :=
  CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (representation A K β hβ hker).rangeRestrict
    (representation A K β hβ hker).rangeRestrict_surjective

end SymmetricSubgroupAsymptotics.CFSGSerreRepresentationDescent
