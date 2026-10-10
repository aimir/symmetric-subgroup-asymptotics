import SymmetricSubgroupAsymptotics.BinaryPairAffineChart
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart
import SymmetricSubgroupAsymptotics.PermutationalWreathLinearRepresentation
import SymmetricSubgroupAsymptotics.TransitiveMonomialCyclic

/-!
# The ternary signed representation of a literal binary pair frame

The affine coordinates of a binary pair frame give a homomorphism into the
literal permutational wreath product.  Composing its function
representation with the faithful sign action on `F3` produces the full
ternary signed coordinate module.  The formulas below retain both the
original source group and the original pair coordinates.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

open OddMarkerTernaryChart

variable {X I : Type} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- The faithful one-dimensional ternary representation of one binary
flip. -/
def ternarySignRepresentation :
    Representation (ZMod 3) (Multiplicative (ZMod 2)) (ZMod 3) where
  toFun s := signScalar s • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro z
    simp only [signScalar_one, one_smul, LinearMap.id_apply,
      Module.End.one_apply]
  map_mul' s t := by
    apply LinearMap.ext
    intro z
    change signScalar (s * t) * z = signScalar s * (signScalar t * z)
    rw [signScalar_mul, mul_assoc]

@[simp] theorem ternarySignRepresentation_apply
    (s : Multiplicative (ZMod 2)) (z : ZMod 3) :
    ternarySignRepresentation s z = signScalar s * z := by
  rfl

/-- The complete affine pair coordinates as an element of the literal
binary permutational wreath product. -/
def affineWreathEmbedding :
    G →* PermutationalWreathProduct
      (Multiplicative (ZMod 2)) F.top.range I where
  toFun u :=
    { left := fun i ↦ Multiplicative.ofAdd (F.affineTranslation u i)
      right := F.top.rangeRestrict u }
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      simpa only using congrArg Multiplicative.ofAdd
        (congrFun F.affineTranslation_one i)
    · exact map_one F.top.rangeRestrict
  map_mul' u v := by
    apply PermutationalWreathProduct.ext
    · funext i
      have h := congrFun (F.affineTranslation_mul u v) i
      simpa only [PermutationalWreathProduct.mul_left, Pi.mul_apply,
        permutationFunctionRepresentation_apply, add_comm] using
          congrArg Multiplicative.ofAdd h
    · exact map_mul F.top.rangeRestrict u v

@[simp] theorem affineWreathEmbedding_left
    (u : G) (i : I) :
    (affineWreathEmbedding F u).left i =
      Multiplicative.ofAdd (F.affineTranslation u i) := rfl

@[simp] theorem affineWreathEmbedding_right
    (u : G) :
    (affineWreathEmbedding F u).right = F.top.rangeRestrict u := rfl

/-- The full ternary signed coordinate representation attached to the
literal pair frame. -/
def ternarySignedRepresentation : Representation (ZMod 3) G (I → ZMod 3) :=
  (PermutationalWreathProduct.functionRepresentation
    (Q := F.top.range) (I := I) ternarySignRepresentation).comp
      (affineWreathEmbedding F)

@[simp] theorem ternarySignedRepresentation_apply
    (u : G) (v : I → ZMod 3) (i : I) :
    ternarySignedRepresentation F u v i =
      signScalar (Multiplicative.ofAdd (F.affineTranslation u i)) *
        v ((F.top u)⁻¹ i) := by
  rfl

/-- On the literal pair kernel the signed representation is diagonal with
the exact coordinate characters used by `CoordinateSign`. -/
theorem ternarySignedRepresentation_kernel_apply
    (k : F.top.ker) (v : I → ZMod 3) (i : I) :
    ternarySignedRepresentation F k.1 v i =
      signScalar (Multiplicative.ofAdd (F.bits k i)) * v i := by
  rw [ternarySignedRepresentation_apply, F.affineTranslation_kernel]
  have hk : F.top k.1 = 1 := k.2
  rw [hk]
  rfl

/-- Every original element transports a coordinate delta to the top image
of that coordinate, multiplied by an invertible ternary sign. -/
theorem ternarySignedRepresentation_single
    (u : G) (i : I) :
    let c := signScalar
      (Multiplicative.ofAdd (F.affineTranslation u (F.top u i)))
    c ≠ 0 ∧
      ternarySignedRepresentation F u (Pi.single i 1) =
        Pi.single (F.top u i) c := by
  let c := signScalar
    (Multiplicative.ofAdd (F.affineTranslation u (F.top u i)))
  have hc : c ≠ 0 := by
    exact (signUnitHom
      (Multiplicative.ofAdd
        (F.affineTranslation u (F.top u i)))).ne_zero
  refine ⟨hc, ?_⟩
  funext j
  by_cases hj : j = F.top u i
  · subst j
    rw [ternarySignedRepresentation_apply]
    change signScalar
        (Multiplicative.ofAdd (F.affineTranslation u (F.top u i))) *
          (Pi.single i (1 : ZMod 3) : I → ZMod 3)
            ((Equiv.symm (F.top u)) (F.top u i)) =
        (Pi.single (F.top u i)
          (signScalar
            (Multiplicative.ofAdd (F.affineTranslation u (F.top u i)))) :
            I → ZMod 3) (F.top u i)
    have hinv : (Equiv.symm (F.top u)) (F.top u i) = i :=
      (F.top u).symm_apply_apply i
    rw [hinv, Pi.single_eq_same, Pi.single_eq_same, mul_one]
  · have hpre : (F.top u)⁻¹ j ≠ i := by
      intro h
      apply hj
      calc
        j = F.top u ((F.top u)⁻¹ j) :=
          ((F.top u).apply_symm_apply j).symm
        _ = F.top u i := congrArg (F.top u) h
    simp only [ternarySignedRepresentation_apply,
      Pi.single_eq_of_ne hpre, Pi.single_eq_of_ne hj, mul_zero]

/-- The full signed coordinate module is cyclic whenever the original pair
action is transitive.  Later applications use the same argument on one
sign fibre inside its literal stabilizer. -/
theorem ternarySignedRepresentation_generated_one
    [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X) :
    RepresentationGeneratedBy (ternarySignedRepresentation F) 1 := by
  letI : MulAction.IsPretransitive G X := htrans
  letI : MulAction G I := MulAction.compHom I F.top
  have htop : MulAction.IsPretransitive G I := by
    letI : MulAction.IsPretransitive F.top.range I := F.top_pretransitive
    constructor
    intro i j
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    exact ⟨u, ht⟩
  apply representationGeneratedBy_one_of_transitive_monomial
    F.top (ternarySignedRepresentation F) htop
  intro u i
  let c := signScalar
    (Multiplicative.ofAdd (F.affineTranslation u (F.top u i)))
  exact ⟨c, ternarySignedRepresentation_single F u i⟩

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
