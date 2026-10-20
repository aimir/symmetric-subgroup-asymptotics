import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathUniform
import SymmetricSubgroupAsymptotics.BinaryPlaneNontrivialCubicFixedFree

/-! The literal odd kernel of an actual binary-plane linear wreath subgroup.
All maps retain the subgroup inclusion, rather than replacing its image by
an abstract order-compatible group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernel
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathNormalGenerators

variable {R I : Type} [Group R] [MulAction R I] [Fintype I] [DecidableEq I]

abbrev Sign := TernarySignedPermutationSubgroupSocles.SignModel
  (TernaryPermutationWreathEmbedding.signs (R := R) (I := I))

def signProjection (C : Subgroup (W (R := R) (I := I))) :
    C →* Sign (R := R) (I := I) :=
  TernaryPermutationWreathEmbedding.signMap.comp
    ((wreathMap (R := R) (I := I)).comp C.subtype)

abbrev oddKernel (C : Subgroup (W (R := R) (I := I))) :=
  (signProjection C).ker

variable (C : Subgroup (W (R := R) (I := I)))

theorem top_one (g : oddKernel C) :
    (((g : C) : W (R := R) (I := I)).right) = 1 := by
  have hg : signProjection C (g : C)=1 := g.property
  exact congrArg (fun z : Sign (R := R) (I := I) => z.right) hg

/-- Actual local projection of the literal odd kernel; its top is already
proved trivial, so these are genuine homomorphisms. -/
def localLinear (i : I) : oddKernel C →* Linear where
  toFun g := ((g : C) : W (R := R) (I := I)).left i
  map_one' := rfl
  map_mul' g h := by
    change ((((g : C) : W (R := R) (I := I)) *
      ((h : C) : W (R := R) (I := I))).left i) = _
    rw [PermutationalWreathProduct.mul_left]
    change ((g : C) : W (R := R) (I := I)).left i *
      ((h : C) : W (R := R) (I := I)).left
        (((g : C) : W (R := R) (I := I)).right⁻¹ • i) =
      ((g : C) : W (R := R) (I := I)).left i *
        ((h : C) : W (R := R) (I := I)).left i
    rw [top_one C g,inv_one,one_smul]

theorem local_even (i : I) (g : oddKernel C) :
    oddMarkerSign (toThree (localLinear C i g))=1 := by
  have hg : signProjection C (g : C)=1 := g.property
  have hi := congrArg (fun z : Sign (R := R) (I := I) => z.left.toAdd.val i) hg
  apply Multiplicative.toAdd.injective
  exact hi

private theorem even_cubic : ∀ g : Equiv.Perm (Fin 3),
    oddMarkerSign g=1 → g^3=1 := by decide +kernel

theorem local_cubic (i : I) (g : oddKernel C) :
    localLinear C i g ^ 3=1 := by
  apply toThree_injective
  rw [map_pow,map_one]
  exact even_cubic _ (local_even C i g)

/-- Nontrivial actual local projections imply the entire binary translation
module has no odd-kernel invariants. Correlations between coordinates are
allowed; independent local Singer elements are not assumed. -/
theorem fixedFree
    (hlocal : ∀ i : I, ∃ g : oddKernel C, localLinear C i g≠1)
    (v : I → Plane)
    (hv : ∀ g : oddKernel C,
      BinaryPlaneCyclicWreathUniform.representation C (g : C) v=v) : v=0 := by
  funext i
  obtain ⟨g,hg⟩ := hlocal i
  apply BinaryPlaneNontrivialCubicFixedFree.fixedFree
    (localLinear C i g) (local_cubic C i g) hg
  have hi := congrFun (hv g) i
  change localLinear C i g
    (v ((((g : C) : W (R := R) (I := I)).right)⁻¹ • i)) = v i at hi
  rw [top_one C g,inv_one,one_smul] at hi
  exact hi

end SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernel
