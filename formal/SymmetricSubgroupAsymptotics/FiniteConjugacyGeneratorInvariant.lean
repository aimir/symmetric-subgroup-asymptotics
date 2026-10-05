import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-!
# Pairwise class separation from a checked generator invariant

The selected emitter may label elements by any compact class invariant.  It
only checks invariance under conjugation by the literal ambient generators.
When those generators are full, the generic theorem upgrades the local tests
to all conjugators and proves that differently labelled representatives are
not conjugate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G ι Code : Type*} [Group G] {c : ℕ}

/-- Conjugators which preserve a displayed code on every group element. -/
def conjugacyCodeStabilizer (code : G → Code) : Subgroup G where
  carrier := {g | ∀ x, code (g * x * g⁻¹) = code x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    calc
      code ((a * b) * x * (a * b)⁻¹) =
          code (a * (b * x * b⁻¹) * a⁻¹) := by
        congr 1
        group
      _ = code (b * x * b⁻¹) := ha _
      _ = code x := hb _
  inv_mem' := by
    intro a ha x
    have h := (ha (a⁻¹ * x * a)).symm
    convert h using 1 <;> group

/-- A compact class-code certificate on a full literal generator tuple. -/
structure FiniteConjugacyGeneratorInvariant
    (ambient : ι → G) (representative : Fin c → G) where
  Code : Type*
  code : G → Code
  generator_invariant : ∀ i x,
    code (ambient i * x * (ambient i)⁻¹) = code x
  representative_injective :
    Function.Injective (fun i => code (representative i))

namespace FiniteConjugacyGeneratorInvariant

variable {ambient : ι → G} {representative : Fin c → G}
    (D : FiniteConjugacyGeneratorInvariant ambient representative)

include D

/-- Generator invariance extends to every literal conjugator. -/
theorem invariant (ambient_full :
    Subgroup.closure (Set.range ambient) = ⊤)
    (g x : G) : D.code (g * x * g⁻¹) = D.code x := by
  have hle : Subgroup.closure (Set.range ambient) ≤
      conjugacyCodeStabilizer D.code := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact D.generator_invariant i
  have htop : conjugacyCodeStabilizer D.code = ⊤ := by
    apply top_unique
    rw [← ambient_full]
    exact hle
  have hg : g ∈ conjugacyCodeStabilizer D.code := by
    rw [htop]
    trivial
  exact hg x

/-- Distinct representative codes prove the exact separation premise of the
sparse class-cardinality cover. -/
theorem separated (ambient_full :
    Subgroup.closure (Set.range ambient) = ⊤) :
    ∀ i j, IsConj (representative i) (representative j) → i = j := by
  intro i j hij
  obtain ⟨g, hg⟩ := isConj_iff.mp hij
  apply D.representative_injective
  have hcode := D.invariant ambient_full g (representative i)
  rw [hg] at hcode
  exact hcode.symm

end FiniteConjugacyGeneratorInvariant

end SymmetricSubgroupAsymptotics

end
