import SymmetricSubgroupAsymptotics.CFSGFieldRootTorusConjugacy

/-! Scaling the actual additive parameter of a root homomorphism. A
nonzero scalar preserves both its literal image and injectivity. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGFieldScaledRootHom
variable {K G : Type*} [Field K] [Group G]

def scalarHom (c : K) : Multiplicative K →* Multiplicative K where
  toFun a := Multiplicative.ofAdd (c * a.toAdd)
  map_one' := by change Multiplicative.ofAdd (c * 0) = 1; rw [mul_zero]; rfl
  map_mul' a b := by
    change Multiplicative.ofAdd (c * (a.toAdd + b.toAdd)) =
      Multiplicative.ofAdd (c * a.toAdd + c * b.toAdd)
    rw [mul_add]

theorem scalarHom_injective (c : K) (hc : c ≠ 0) : Function.Injective (scalarHom c) := by
  intro a b he
  apply Multiplicative.toAdd.injective
  apply mul_left_cancel₀ hc
  exact congrArg Multiplicative.toAdd he

theorem scalarHom_surjective (c : K) (hc : c ≠ 0) : Function.Surjective (scalarHom c) := by
  intro a
  refine ⟨Multiplicative.ofAdd (a.toAdd / c), ?_⟩
  apply Multiplicative.toAdd.injective
  change c * (a.toAdd / c) = a.toAdd
  field_simp

def scaledHom (u : Multiplicative K →* G) (c : K) : Multiplicative K →* G := u.comp (scalarHom c)

theorem scaledHom_injective (u : Multiplicative K →* G) (hu : Function.Injective u)
    (c : K) (hc : c ≠ 0) : Function.Injective (scaledHom u c) :=
  hu.comp (scalarHom_injective c hc)

theorem scaledHom_range (u : Multiplicative K →* G) (c : K) (hc : c ≠ 0) :
    (scaledHom u c).range = u.range := by
  ext y
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨scalarHom c a, ha⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := scalarHom_surjective c hc a
    refine ⟨b, ?_⟩
    change u (scalarHom c b) = y
    rw [hb]
    exact ha

end SymmetricSubgroupAsymptotics.CFSGFieldScaledRootHom
