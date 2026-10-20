import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.RepresentationTheory.Basic

/-!
Descent and extension of the actual point-stabilizer homomorphism.

Canonical extension of a local homomorphism from H to L through an
actual quotient pi : L -> Q. In the pair application, H is the point
stabilizer, L the pair stabilizer, Q the stabilizer in the eight-pair top,
and ker pi is the literal global pair kernel inside L.

Surjectivity of pi on H and kernel annihilation are group-theoretic
obligations. This file proves the extension from those exact obligations;
it does not assume an extension, splitting, or desired module bound.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PairLocalQuotientExtension

variable {H L Q C : Type} [Group H] [Group L] [Group Q] [Group C]
  (i : H →* L) (pi : L →* Q) (f : H →* C)
  (honto : Function.Surjective (pi.comp i))
  (hker : (pi.comp i).ker ≤ f.ker)

/-- The original local map on the pair-top stabilizer quotient. -/
def descended : Q →* C :=
  (pi.comp i).liftOfSurjective honto ⟨f, hker⟩

@[simp] theorem descended_apply (h : H) :
    descended i pi f honto hker (pi (i h)) = f h :=
  MonoidHom.liftOfRightInverse_comp_apply (pi.comp i)
    (Function.surjInv honto) (Function.rightInverse_surjInv honto) _ h

/-- Extension to the pair stabilizer, killing the original pair kernel. -/
def extension : L →* C :=
  (descended i pi f honto hker).comp pi

@[simp] theorem extension_apply (h : H) :
    extension i pi f honto hker (i h) = f h :=
  descended_apply i pi f honto hker h

theorem extension_comp :
    (extension i pi f honto hker).comp i = f := by
  ext h
  exact extension_apply i pi f honto hker h

theorem kernel_le_extension_kernel :
    pi.ker ≤ (extension i pi f honto hker).ker := by
  intro l hl
  change descended i pi f honto hker (pi l) = 1
  rw [MonoidHom.mem_ker.mp hl, map_one]

theorem descended_surjective (hf : Function.Surjective f) :
    Function.Surjective (descended i pi f honto hker) := by
  intro c
  obtain ⟨h, rfl⟩ := hf c
  exact ⟨pi (i h), descended_apply i pi f honto hker h⟩

theorem extension_surjective (hf : Function.Surjective f) :
    Function.Surjective (extension i pi f honto hker) := by
  intro c
  obtain ⟨h, rfl⟩ := hf c
  exact ⟨i h, extension_apply i pi f honto hker h⟩

/-- Product coverage by the actual quotient kernel and H proves the needed
onto statement on H. No complement to the kernel is requested. -/
theorem restricted_surjective_of_kernel_factorization
    (hpi : Function.Surjective pi)
    (hfactor : ∀ l : L, ∃ k : pi.ker, ∃ h : H, (k : L) * i h = l) :
    Function.Surjective (pi.comp i) := by
  intro q
  obtain ⟨l, rfl⟩ := hpi q
  obtain ⟨k, h, rfl⟩ := hfactor l
  refine ⟨h, ?_⟩
  change pi (i h) = pi ((k : L) * i h)
  rw [map_mul, MonoidHom.mem_ker.mp k.property, one_mul]

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

/-- The extension is compatible with the unchanged local target
representation; all its twists are inherited from the original map. -/
def extendedRepresentation (tau : Representation k C V) :
    Representation k L V :=
  tau.comp (extension i pi f honto hker)

@[simp] theorem extendedRepresentation_apply
    (tau : Representation k C V) (h : H) :
    extendedRepresentation i pi f honto hker tau (i h) = tau (f h) := by
  change tau (extension i pi f honto hker (i h)) = tau (f h)
  rw [extension_apply]

end SymmetricSubgroupAsymptotics.PairLocalQuotientExtension

end

