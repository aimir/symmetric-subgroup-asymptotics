import SymmetricSubgroupAsymptotics.OriginalEquivariantQuotientEmbedding
import Mathlib.RepresentationTheory.Invariants

/-! Fixed-free restriction survives actual equivariant subquotients when
the finite acting group has invertible order. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace RepresentationFixedFreeQuotient

variable {k G V W : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- An actual equivariant injection transports absence of fixed vectors. -/
theorem of_injective (rho : Representation k G V) (sigma : Representation k G W)
    (i : sigma.IntertwiningMap rho) (hi : Function.Injective i)
    (hfixed : ∀ v : V, (∀ g : G, rho g v = v) → v = 0) :
    ∀ w : W, (∀ g : G, sigma g w = w) → w = 0 := by
  intro w hw
  have hiw : i w = 0 := hfixed (i w) (fun g ↦ by
    rw [← Representation.IntertwiningMap.isIntertwining sigma rho i g w, hw g])
  apply hi
  simpa only [map_zero] using hiw

/-- Maschke is used only for the finite odd separator, even if the full
original group has even order. The epimorphism and its original target
are retained explicitly. -/
theorem of_surjective [Finite G] [NeZero (Nat.card G : k)]
    (rho : Representation k G V) (sigma : Representation k G W)
    (q : rho.IntertwiningMap sigma) (hq : Function.Surjective q)
    (hfixed : ∀ v : V, (∀ g : G, rho g v = v) → v = 0) :
    ∀ w : W, (∀ g : G, sigma g w = w) → w = 0 := by
  obtain ⟨i, hi⟩ := original_equivariant_quotient_embedding rho sigma q hq
  exact of_injective rho sigma i hi hfixed

end RepresentationFixedFreeQuotient
end SymmetricSubgroupAsymptotics
