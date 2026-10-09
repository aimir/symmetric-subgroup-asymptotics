import SymmetricSubgroupAsymptotics.BinaryPairFrameSignTopAction
import SymmetricSubgroupAsymptotics.BinaryPairFrameTernarySignedRepresentation
import SymmetricSubgroupAsymptotics.CoprimeCyclicRestrictionGenerators

/-!
# Cyclic submodules on a binary-sized sign fibre

Fix one realized pair-kernel character.  Its literal stabilizer acts on the
coordinates carrying that character, and the affine pair coordinates give
the resulting ternary monomial representation.  When the fibre has
power-of-two size, its transitive Sylow subgroup is coprime to `F3`.
Maschke projection then makes every subrepresentation on that fibre cyclic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

open OddMarkerTernaryChart

variable {X I : Type*} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- Restrict the affine wreath coordinates to the stabilizer of one sign
and to the coordinates in that sign fibre. -/
def signFiberWreathEmbedding
    (chi : CoordinateSign F) :
    MulAction.stabilizer G chi →*
      PermutationalWreathProduct (Multiplicative (ZMod 2))
        (MulAction.stabilizer G chi)
        {i : I // coordinateSign F i = chi} where
  toFun u :=
    { left := fun i ↦ Multiplicative.ofAdd
        (F.affineTranslation u.1 i.1)
      right := u }
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      apply Multiplicative.toAdd.injective
      simp only [Multiplicative.toAdd_ofAdd, Pi.one_apply,
        Multiplicative.toAdd_one]
      exact congrFun F.affineTranslation_one i.1
    · rfl
  map_mul' u v := by
    apply PermutationalWreathProduct.ext
    · funext i
      apply Multiplicative.toAdd.injective
      change F.affineTranslation (u.1 * v.1) i.1 =
        F.affineTranslation u.1 i.1 +
          F.affineTranslation v.1 ((F.top u.1)⁻¹ i.1)
      have h := congrFun (F.affineTranslation_mul u.1 v.1) i.1
      simpa only [permutationFunctionRepresentation_apply, add_comm] using h
    · rfl

/-- The monomial ternary module supported on one literal sign fibre. -/
def signFiberRepresentation
    (chi : CoordinateSign F) :
    Representation (ZMod 3) (MulAction.stabilizer G chi)
      ({i : I // coordinateSign F i = chi} → ZMod 3) :=
  (PermutationalWreathProduct.functionRepresentation
    (Q := MulAction.stabilizer G chi)
    (I := {i : I // coordinateSign F i = chi})
    ternarySignRepresentation).comp
      (signFiberWreathEmbedding F chi)

@[simp] theorem signFiberRepresentation_apply
    (chi : CoordinateSign F)
    (u : MulAction.stabilizer G chi)
    (v : {i : I // coordinateSign F i = chi} → ZMod 3)
    (i : {i : I // coordinateSign F i = chi}) :
    signFiberRepresentation F chi u v i =
      signScalar (Multiplicative.ofAdd (F.affineTranslation u.1 i.1)) *
        v (u⁻¹ • i) := by
  rfl

/-- The restricted signed action is monomial on the literal fibre basis. -/
theorem signFiberRepresentation_single
    (chi : CoordinateSign F)
    (u : MulAction.stabilizer G chi)
    (i : {i : I // coordinateSign F i = chi}) :
    let c := signScalar (Multiplicative.ofAdd
      (F.affineTranslation u.1 (u • i).1))
    c ≠ 0 ∧
      signFiberRepresentation F chi u (Pi.single i 1) =
        Pi.single (u • i) c := by
  let c := signScalar (Multiplicative.ofAdd
    (F.affineTranslation u.1 (u • i).1))
  have hc : c ≠ 0 := by
    exact (signUnitHom (Multiplicative.ofAdd
      (F.affineTranslation u.1 (u • i).1))).ne_zero
  refine ⟨hc, ?_⟩
  funext j
  by_cases hj : j = u • i
  · subst j
    simp only [signFiberRepresentation_apply, inv_smul_smul,
      Pi.single_eq_same, mul_one, c]
  · have hpre : u⁻¹ • j ≠ i := by
      intro h
      apply hj
      have := congrArg (u • ·) h
      simpa only [smul_inv_smul] using this
    simp [signFiberRepresentation_apply, Pi.single_apply, hj, hpre]

/-- A binary group has order invertible in `F3`. -/
theorem neZero_card_zmod_three_of_isPGroup_two
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) : NeZero (Nat.card P : ZMod 3) := by
  letI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  constructor
  rw [ha, Nat.cast_pow]
  exact pow_ne_zero a (by norm_num : (2 : ZMod 3) ≠ 0)

/-- Every subrepresentation on a power-of-two sign fibre is cyclic. -/
theorem signFiber_uniformSubrepresentationGeneratorBound_one
    [Finite X] [Finite I]
    (htrans : MulAction.IsPretransitive G X)
    (chi : CoordinateSign F) (a : ℕ)
    (hcard : Nat.card {i : I // coordinateSign F i = chi} = 2 ^ a) :
    UniformSubrepresentationGeneratorBound
      (signFiberRepresentation F chi) 1 := by
  obtain ⟨P, hP, hPtrans⟩ :=
    exists_transitive_binarySubgroup_of_coordinateSignFiber
      F htrans chi a hcard
  letI : NeZero (Nat.card P : ZMod 3) :=
    neZero_card_zmod_three_of_isPGroup_two hP
  apply uniformSubrepresentationGeneratorBound_of_coprime_cyclic_restriction
    (signFiberRepresentation F chi) P
  let topP : P →* Equiv.Perm
      {i : I // coordinateSign F i = chi} :=
    (coordinateSignFiberTopHom F chi).comp P.subtype
  apply representationGeneratedBy_one_of_transitive_monomial topP
    ((signFiberRepresentation F chi).comp P.subtype) hPtrans
  intro u i
  let c := signScalar (Multiplicative.ofAdd
    (F.affineTranslation u.1.1 (u.1 • i).1))
  refine ⟨c, ?_⟩
  simpa only [Representation.comp_apply, MonoidHom.comp_apply, topP, c] using
    (signFiberRepresentation_single F chi u.1 i)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
