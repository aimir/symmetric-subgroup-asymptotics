import SymmetricSubgroupAsymptotics.CocycleLifts

/-!
# Kernel cocycles are determined by a generating tuple

This is the multiplicative counterpart of `CocycleGeneratorBound`.  It is
used before choosing additive coordinates: two crossed homomorphisms into
the literal kernel which agree on generators agree on the whole source.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {J Q B ι : Type*} [Group J] [Group Q] [Group B]

/-- Values of a literal kernel cocycle on an original tuple. -/
def kernelCocycleGeneratorEvaluation (pi : Q →* B) (f₀ : J →* Q)
    (generators : ι → J) :
    KernelCocycle pi f₀ → (ι → pi.ker) :=
  fun z i ↦ z.1 (generators i)

private theorem kernelCocycle_value_one (pi : Q →* B) (f₀ : J →* Q)
    (z : KernelCocycle pi f₀) : z.1 1 = 1 := by
  apply Subtype.ext
  have h := z.2 1 1
  simp only [map_one, mul_one, inv_one] at h
  exact mul_left_cancel (show (z.1 1 : Q) * (z.1 1 : Q) =
      (z.1 1 : Q) * 1 by simpa using h.symm)

private theorem kernelCocycle_value_inv (pi : Q →* B) (f₀ : J →* Q)
    (z : KernelCocycle pi f₀) (x : J) :
    (z.1 x⁻¹ : Q) = (f₀ x)⁻¹ * (z.1 x : Q)⁻¹ * f₀ x := by
  have h := z.2 x x⁻¹
  have h1 : (z.1 1 : Q) = 1 :=
    congrArg Subtype.val (kernelCocycle_value_one pi f₀ z)
  simp only [mul_inv_cancel] at h
  rw [h1] at h
  have h' := congrArg
    (fun q : Q ↦ (f₀ x)⁻¹ * (z.1 x : Q)⁻¹ * q * f₀ x) h
  group at h' ⊢
  exact h'.symm

/-- Evaluation is injective as soon as the displayed tuple generates the
actual source.  No commutativity of the kernel is needed. -/
theorem kernelCocycleGeneratorEvaluation_injective
    (pi : Q →* B) (f₀ : J →* Q) (generators : ι → J)
    (hgen : Subgroup.closure (Set.range generators) = ⊤) :
    Function.Injective (kernelCocycleGeneratorEvaluation pi f₀ generators) := by
  intro z z' heq
  have hone : z.1 1 = z'.1 1 := by
    rw [kernelCocycle_value_one, kernelCocycle_value_one]
  let K : Subgroup J :=
    { carrier := {x | z.1 x = z'.1 x}
      one_mem' := hone
      mul_mem' := by
        intro x y hx hy
        apply Subtype.ext
        change (z.1 (x * y) : Q) = (z'.1 (x * y) : Q)
        rw [z.2, z'.2, hx, hy]
      inv_mem' := by
        intro x hx
        apply Subtype.ext
        rw [kernelCocycle_value_inv, kernelCocycle_value_inv,
          congrArg Subtype.val hx] }
  have hclosure : Subgroup.closure (Set.range generators) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact congrFun heq i
  apply Subtype.ext
  funext x
  exact hclosure (by rw [hgen]; trivial)

/-- A finite kernel gives the corresponding generator-power cardinal bound
for the full crossed-homomorphism fibre. -/
theorem kernelCocycle_card_le_generator_power
    (pi : Q →* B) [Finite (pi.ker)] (f₀ : J →* Q) (d : ℕ)
    (generators : Fin d → J)
    (hgen : Subgroup.closure (Set.range generators) = ⊤) :
    Nat.card (KernelCocycle pi f₀) ≤ Nat.card pi.ker ^ d := by
  calc
    Nat.card (KernelCocycle pi f₀) ≤ Nat.card (Fin d → pi.ker) :=
      Nat.card_le_card_of_injective
        (kernelCocycleGeneratorEvaluation pi f₀ generators)
        (kernelCocycleGeneratorEvaluation_injective pi f₀ generators hgen)
    _ = Nat.card pi.ker ^ d := by rw [Nat.card_fun, Nat.card_fin]

end SymmetricSubgroupAsymptotics

end
