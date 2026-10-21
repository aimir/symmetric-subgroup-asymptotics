import SymmetricSubgroupAsymptotics.CFSGSerreRepresentationDescent

/-! Any genuine divided-power intertwiner gives an action on its actual
image, without assuming the map onto an independently specified target.
All image restrictions are obtained from the same source divided powers. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreImageRepresentation
open CFSG.Models.Chevalley CFSGSerreRepresentationDescent
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (β : Space A K →ₗ[K] V) (D : Bool → Fin n → ℕ → Module.End K V)
    (hD : ∀ neg i k x, β ((integralOperator A neg i k).baseChange K x) = D neg i k (β x))
include hD

theorem range_stable (neg : Bool) (i : Fin n) (k : ℕ) (y : V) (hy : y ∈ β.range) :
    D neg i k y ∈ β.range := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨(integralOperator A neg i k).baseChange K x, hD neg i k x⟩

def rangeOperator (neg : Bool) (i : Fin n) (k : ℕ) : Module.End K β.range :=
  (D neg i k).restrict (range_stable A K β D hD neg i k)

theorem range_intertwines (neg : Bool) (i : Fin n) (k : ℕ) (x : Space A K) :
    β.rangeRestrict ((integralOperator A neg i k).baseChange K x) =
      rangeOperator A K β D hD neg i k (β.rangeRestrict x) := by
  apply Subtype.ext
  exact hD neg i k x

def imageRepresentation : Model A K →* (β.range ≃ₗ[K] β.range) :=
  representation A K β.rangeRestrict β.surjective_rangeRestrict
    (kernel_stable_of_intertwiners A K β.rangeRestrict
      (rangeOperator A K β D hD) (range_intertwines A K β D hD))

theorem imageRepresentation_intertwines (g : Model A K) (x : Space A K) :
    (imageRepresentation A K β D hD g (β.rangeRestrict x)).val = β (g.val x) := by
  exact congrArg Subtype.val (representation_intertwines A K β.rangeRestrict
    β.surjective_rangeRestrict
    (kernel_stable_of_intertwiners A K β.rangeRestrict
      (rangeOperator A K β D hD) (range_intertwines A K β D hD)) g x)

end SymmetricSubgroupAsymptotics.CFSGSerreImageRepresentation
