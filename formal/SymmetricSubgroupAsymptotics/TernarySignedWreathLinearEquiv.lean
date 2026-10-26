import SymmetricSubgroupAsymptotics.TernaryMonomialCocycle
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart
import SymmetricSubgroupAsymptotics.PermutationalWreathFinite

/-! The faithful linear-equivalence action of the literal signed
permutation wreath product on its original ternary coordinate module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernarySignedWreathLinearEquiv
open OddMarkerTernaryChart

variable (I : Type)

abbrev Model := PermutationalWreathProduct (Multiplicative (ZMod 2)) (Equiv.Perm I) I

def permutationHom : Model I →* Equiv.Perm I := PermutationalWreathProduct.rightHom

def coefficient (g : Model I) (i : I) : (ZMod 3)ˣ := signUnitHom (g.left i)

private theorem coefficient_one (i : I) :
    (coefficient I 1 i : ZMod 3)=1 := by
  exact congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) (map_one signUnitHom)

private theorem coefficient_mul (g h : Model I) (i : I) :
    (coefficient I (g*h) i : ZMod 3)=
      (coefficient I g i : ZMod 3)*(coefficient I h ((permutationHom I) g⁻¹ i) : ZMod 3) :=
  signScalar_mul (g.left i) (h.left (g.right⁻¹ i))

def linearHom : Model I →* ((I → ZMod 3) ≃ₗ[ZMod 3] (I → ZMod 3)) :=
  TernaryMonomialCocycle.linearAction (permutationHom I)
    (fun g i => (coefficient I g i : ZMod 3)) (coefficient_one I) (coefficient_mul I)

theorem linearHom_apply (g : Model I) (v : I → ZMod 3) (i : I) :
    linearHom I g v i=(coefficient I g i : ZMod 3)*v ((permutationHom I g).symm i) := by
  rfl

theorem linearHom_injective : Function.Injective (linearHom I) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hr : g.right=1 := by
    apply Equiv.ext
    intro i
    by_contra hi
    change g.right i≠i at hi
    have h := congrArg
      (fun e : (I → ZMod 3) ≃ₗ[ZMod 3] (I → ZMod 3) =>
        e (Pi.single i (1 : ZMod 3) : I → ZMod 3) (g.right i)) hg
    change (coefficient I g (g.right i) : ZMod 3)*
      (Pi.single i (1 : ZMod 3) : I → ZMod 3) (g.right.symm (g.right i))=
        (Pi.single i (1 : ZMod 3) : I → ZMod 3) (g.right i) at h
    rw [Equiv.symm_apply_apply,Pi.single_eq_same,mul_one,Pi.single_eq_of_ne hi] at h
    exact (coefficient I g (g.right i)).ne_zero h
  apply PermutationalWreathProduct.ext
  · funext i
    apply signUnitHom_injective
    apply Units.ext
    have h := congrArg
      (fun e : (I → ZMod 3) ≃ₗ[ZMod 3] (I → ZMod 3) => e (fun _ => 1) i) hg
    change (coefficient I g i : ZMod 3)*1=1 at h
    simpa only [mul_one,map_one] using h
  · exact hr

theorem permutationHom_surjective : Function.Surjective (permutationHom I) := by
  intro s
  exact ⟨⟨1,s⟩,rfl⟩

end SymmetricSubgroupAsymptotics.TernarySignedWreathLinearEquiv
