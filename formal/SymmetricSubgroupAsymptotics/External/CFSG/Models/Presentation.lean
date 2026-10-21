import Mathlib.GroupTheory.PresentedGroup

namespace CFSG.Models

/-- Magma's commutator convention; deliberately different from some Lean notation. -/
def commWord {G : Type*} [Group G] (a b : G) : G := a⁻¹ * b⁻¹ * a * b

/-- Magma's right conjugation convention `a^b`. -/
def conjugateWord {G : Type*} [Group G] (a b : G) : G := b⁻¹ * a * b

end CFSG.Models
