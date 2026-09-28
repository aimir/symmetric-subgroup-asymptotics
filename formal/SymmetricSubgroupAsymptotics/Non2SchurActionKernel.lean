import SymmetricSubgroupAsymptotics.Non2SchurRowDegrees

/-!
# The actual action kernel of a Schur row

For an actual simple row, this file keeps its literal kernel in the original
acting group.  The kernel fixes the whole corresponding isotypic socle
component, not merely the selected copy of the simple module.  This is the
module-theoretic input needed before applying the normal-orbit filtration to
the mixed trivial/simple section.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u
variable {k B A : Type u} [Field k] [Group B]
    [AddCommGroup A] [Module k A]

/-- The original group action on the selected simple module. -/
def schurSimpleActionRepresentation
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule) : Representation k B S :=
  Representation.ofModule' S

/-- Its literal kernel inside the original acting group. -/
abbrev schurSimpleActionKernel
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule) : Subgroup B :=
  (schurSimpleActionRepresentation sigma S).ker

theorem mem_schurSimpleActionKernel_iff
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule) (g : B) :
    g ∈ schurSimpleActionKernel sigma S ↔
      ∀ x : S, MonoidAlgebra.single g (1 : k) • x = x := by
  constructor
  · intro hg x
    have hx := LinearMap.congr_fun hg x
    change MonoidAlgebra.single g (1 : k) • x = x at hx
    simpa using hx
  · intro hg
    apply LinearMap.ext
    intro x
    change MonoidAlgebra.single g (1 : k) • x = x
    exact hg x

/-- Every element of the actual row kernel fixes the complete isotypic
component carrying all copies of that simple module in the socle. -/
theorem schurSimpleActionKernel_fixes_isotypic
    [FiniteDimensional k A]
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule)
    [IsSimpleModule k[B] S]
    (g : schurSimpleActionKernel sigma S)
    (y : isotypicComponent k[B] sigma.asModule S) :
    MonoidAlgebra.single (g : B) (1 : k) • y = y := by
  let e := schurSocleDecomposition
    (k := k) (R := k[B]) (A := sigma.asModule) (X := S)
  apply e.injective
  rw [e.map_smul]
  ext i
  exact congrArg Subtype.val
    ((mem_schurSimpleActionKernel_iff sigma S (g : B)).mp g.property (e y i))

/-- The literal binary subspace consisting of the whole invariant row and
the complete selected isotypic socle row. -/
def schurMixedSocleSubspace
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule) : Submodule k sigma.asModule :=
  sigma.invariants.map sigma.asModuleEquiv.symm.toLinearMap ⊔
    (isotypicComponent k[B] sigma.asModule S).restrictScalars k

/-- The same actual row kernel fixes the complete mixed trivial/simple
subspace pointwise. -/
theorem schurSimpleActionKernel_fixes_mixedSocle
    [FiniteDimensional k A]
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule)
    [IsSimpleModule k[B] S]
    (g : schurSimpleActionKernel sigma S)
    (y : schurMixedSocleSubspace sigma S) :
    MonoidAlgebra.single (g : B) (1 : k) • (y : sigma.asModule) = y := by
  obtain ⟨u, hu, v, hv, hy⟩ := Submodule.mem_sup.mp y.property
  rw [← hy, smul_add]
  congr 1
  · obtain ⟨a, ha, rfl⟩ := hu
    rw [Representation.single_smul, one_smul]
    change sigma (g : B) a = a
    exact ha (g : B)
  · exact congrArg Subtype.val
      (schurSimpleActionKernel_fixes_isotypic sigma S g ⟨v, hv⟩)

end SymmetricSubgroupAsymptotics

end
