import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernel
import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient

/-! An actual invariant binary sign module has a faithful action on two
points per original block. No whole sign module or pure block complement
is inferred for a subgroup embedded through this action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySignWreathPointAction
open SemidirectProduct PermutationalWreathProduct

/-- Literal additive translations of the two-point field. -/
def bitTranslation : Multiplicative (ZMod 2) →* Equiv.Perm (ZMod 2) where
  toFun a := Equiv.addLeft a.toAdd
  map_one' := by
    apply Equiv.ext
    intro x
    change 0 + x = x
    exact zero_add x
  map_mul' a b := by
    apply Equiv.ext
    intro x
    change (a.toAdd + b.toAdd) + x = a.toAdd + (b.toAdd + x)
    exact add_assoc _ _ _

theorem bitTranslation_injective : Function.Injective bitTranslation := by
  intro a b he
  apply Multiplicative.toAdd.injective
  have h := congrArg (fun e : Equiv.Perm (ZMod 2) => e 0) he
  change a.toAdd + 0 = b.toAdd + 0 at h
  simpa only [add_zero] using h

variable {R I : Type} [Group R] [MulAction R I] [Fintype I] [DecidableEq I]
    (E : Subrepresentation
      (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation (R := R) (X := I)))

/-- Keep the actual invariant sign submodule and the original top coordinate. -/
def signWreath : TernarySignedPermutationSubgroupSocles.SignModel E →*
    PermutationalWreathProduct (Multiplicative (ZMod 2)) R I where
  toFun g := ⟨fun i => Multiplicative.ofAdd (g.left.toAdd.val i),g.right⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      rfl
    · rfl
  map_mul' g h := by
    apply PermutationalWreathProduct.ext
    · funext i
      rfl
    · rfl

theorem signWreath_injective : Function.Injective (signWreath E) := by
  intro g h he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact congrArg (fun w : PermutationalWreathProduct (Multiplicative (ZMod 2)) R I =>
      (w.left i).toAdd) he
  · exact congrArg (fun w : PermutationalWreathProduct (Multiplicative (ZMod 2)) R I =>
      w.right) he

/-- Two points above each original block give the actual sign action. -/
def pointHom : TernarySignedPermutationSubgroupSocles.SignModel E →*
    Equiv.Perm (ZMod 2 × I) :=
  (PermutationalWreathProduct.toPerm (D := Equiv.Perm (ZMod 2))
    (Q := R) (I := I) (Lambda := ZMod 2)).comp
      ((mapBase (Q := R) (I := I) bitTranslation).comp (signWreath E))

theorem pointHom_injective [FaithfulSMul R I] [Nonempty I] :
    Function.Injective (pointHom E) := by
  intro g h he
  have hw := PermutationalWreathProduct.toPerm_injective he
  apply signWreath_injective E
  apply PermutationalWreathProduct.ext
  · funext i
    exact bitTranslation_injective (congrArg
      (fun w : PermutationalWreathProduct (Equiv.Perm (ZMod 2)) R I => w.left i) hw)
  · exact congrArg
      (fun w : PermutationalWreathProduct (Equiv.Perm (ZMod 2)) R I => w.right) hw

end SymmetricSubgroupAsymptotics.BinarySignWreathPointAction
