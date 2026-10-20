import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCataloguePairedSixInterfaces
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Exact product and wreath models for the retained paired-six tops

The first action uses diagonal and anti-diagonal ternary coordinates, so
its product identification is proved by explicit commuting factor maps.
The second is the natural two-block wreath action. Both equivalences target
the original literal closures, using forward bindings and reverse words.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PairedSixLiteralModels

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue

abbrev S3 := Equiv.Perm (Fin 3)
abbrev C2 := Multiplicative (ZMod 2)
abbrev Wreath := DegreeSixS3Wreath.G

def rotation : S3 := Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2
def reflection : S3 := Equiv.swap (1 : Fin 3) 2

def pointEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6 where
  toFun
    | .inl i => ![0, 1, 3] i
    | .inr i => ![2, 4, 5] i
  invFun i := ![Sum.inl 0, Sum.inl 1, Sum.inr 0,
    Sum.inl 2, Sum.inr 1, Sum.inr 2] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def action : Wreath →* Equiv.Perm (Fin 6) :=
  pointEquiv.permCongrHom.toMonoidHom.comp
    (C2Wreath.action (MonoidHom.id S3))

theorem action_injective : Function.Injective action :=
  pointEquiv.permCongrHom.injective.comp
    (C2Wreath.action_injective (MonoidHom.id S3) Function.injective_id)

def firstRotation : Wreath := inl (rotation, 1)
def firstReflection : Wreath := inl (reflection, 1)
def diagonalReflection : Wreath := inl (reflection, reflection)
def blockSwap : Wreath := inr C2Wreath.gen

private theorem wreath_eq_iff (x y : Wreath) :
    x = y ↔ x.left = y.left ∧ x.right = y.right :=
  ⟨fun h ↦ ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩,
    fun h ↦ SemidirectProduct.ext h.1 h.2⟩

theorem s3_normal_form (g : S3) :
    g = rotation ^ (g 0).val * reflection ^ (oddMarkerSign g).toAdd.val := by
  revert g
  decide +kernel

namespace Product

abbrev Model := S3 × S3

def diagonalRotation : Wreath := inl (rotation, rotation)
def antiDiagonalRotation : Wreath := inl (rotation, rotation⁻¹)
def firstSign : Wreath := diagonalReflection * blockSwap

def firstFactor : S3 →* Wreath where
  toFun g := diagonalRotation ^ (g 0).val * firstSign ^ (oddMarkerSign g).toAdd.val
  map_one' := by apply SemidirectProduct.ext <;> decide +kernel
  map_mul' := by simp only [wreath_eq_iff]; decide +kernel

def secondFactor : S3 →* Wreath where
  toFun g := antiDiagonalRotation ^ (g 0).val * blockSwap ^ (oddMarkerSign g).toAdd.val
  map_one' := by apply SemidirectProduct.ext <;> decide +kernel
  map_mul' := by simp only [wreath_eq_iff]; decide +kernel

theorem factors_commute (g h : S3) : Commute (firstFactor g) (secondFactor h) := by
  change firstFactor g * secondFactor h = secondFactor h * firstFactor g
  revert g h
  simp only [wreath_eq_iff]
  decide +kernel

def intoWreath : Model →* Wreath :=
  firstFactor.noncommCoprod secondFactor factors_commute

theorem intoWreath_injective : Function.Injective intoWreath := by
  rw [injective_iff_map_eq_one]
  have hcheck : ∀ g : Model, intoWreath g = 1 → g = 1 := by
    simp only [wreath_eq_iff]
    decide +kernel
  exact hcheck

def literalAction : Model →* Equiv.Perm (Fin 6) := action.comp intoWreath

def modelGenerators : Fin 3 → Model :=
  ![(rotation ^ 2, rotation ^ 2), (reflection, reflection), (1, reflection)]

theorem generators_binding (i : Fin 3) :
    literalAction (modelGenerators i) = pairedSix1Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

private def secondLiteralRotation : Equiv.Perm (Fin 6) :=
  pairedSix1Generators 2 * pairedSix1Generators 0 * (pairedSix1Generators 2)⁻¹

private theorem factor_words :
    action diagonalRotation = pairedSix1Generators 0 * secondLiteralRotation ∧
    action antiDiagonalRotation = pairedSix1Generators 0 * secondLiteralRotation⁻¹ ∧
    action firstSign = pairedSix1Generators 1 * pairedSix1Generators 2 ∧
    action blockSwap = pairedSix1Generators 2 := by
  repeat' constructor
  all_goals
    apply Equiv.ext
    intro x
    revert x
    decide +kernel

theorem literalAction_mem (g : Model) : literalAction g ∈ PairedSix1Top := by
  have hg (i : Fin 3) : pairedSix1Generators i ∈ PairedSix1Top :=
    Subgroup.subset_closure (Set.mem_range_self i)
  have hs : secondLiteralRotation ∈ PairedSix1Top :=
    PairedSix1Top.mul_mem (PairedSix1Top.mul_mem (hg 2) (hg 0))
      (PairedSix1Top.inv_mem (hg 2))
  have hd : action diagonalRotation ∈ PairedSix1Top := by
    rw [factor_words.1]
    exact PairedSix1Top.mul_mem (hg 0) hs
  have ha : action antiDiagonalRotation ∈ PairedSix1Top := by
    rw [factor_words.2.1]
    exact PairedSix1Top.mul_mem (hg 0) (PairedSix1Top.inv_mem hs)
  have hf : action firstSign ∈ PairedSix1Top := by
    rw [factor_words.2.2.1]
    exact PairedSix1Top.mul_mem (hg 1) (hg 2)
  have hb : action blockSwap ∈ PairedSix1Top := by
    rw [factor_words.2.2.2]
    exact hg 2
  change action (firstFactor g.1 * secondFactor g.2) ∈ PairedSix1Top
  change action ((diagonalRotation ^ (g.1 0).val *
      firstSign ^ (oddMarkerSign g.1).toAdd.val) *
    (antiDiagonalRotation ^ (g.2 0).val *
      blockSwap ^ (oddMarkerSign g.2).toAdd.val)) ∈ PairedSix1Top
  simp only [map_mul, map_pow]
  exact PairedSix1Top.mul_mem
    (PairedSix1Top.mul_mem (PairedSix1Top.pow_mem hd _) (PairedSix1Top.pow_mem hf _))
    (PairedSix1Top.mul_mem (PairedSix1Top.pow_mem ha _) (PairedSix1Top.pow_mem hb _))

theorem range_eq : literalAction.range = PairedSix1Top := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact literalAction_mem g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : Model ≃* PairedSix1Top :=
  (MonoidHom.ofInjective (f := literalAction)
    (action_injective.comp intoWreath_injective)).trans
    (MulEquiv.subgroupCongr range_eq)

end Product

namespace FullWreath

def modelGenerators : Fin 3 → Wreath := ![firstRotation, firstReflection, blockSwap]

theorem generators_binding (i : Fin 3) :
    action (modelGenerators i) = pairedSix2Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

private theorem conjugate_first (g : S3) :
    blockSwap * inl (g, 1) * blockSwap⁻¹ = (inl (1, g) : Wreath) := by
  revert g
  simp only [wreath_eq_iff]
  decide +kernel

theorem action_mem (g : Wreath) : action g ∈ PairedSix2Top := by
  have hg (i : Fin 3) : action (modelGenerators i) ∈ PairedSix2Top := by
    rw [generators_binding]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hr : action firstRotation ∈ PairedSix2Top := hg 0
  have ht : action firstReflection ∈ PairedSix2Top := hg 1
  have hs : action blockSwap ∈ PairedSix2Top := hg 2
  have hfirst (a : S3) : action (inl (a, 1)) ∈ PairedSix2Top := by
    have hword : (inl (a, 1) : Wreath) =
        firstRotation ^ (a 0).val * firstReflection ^ (oddMarkerSign a).toAdd.val := by
      calc
        (inl (a, 1) : Wreath) =
            inl (rotation ^ (a 0).val * reflection ^ (oddMarkerSign a).toAdd.val, 1) :=
          congrArg (fun a : S3 ↦ (inl (a, 1) : Wreath)) (s3_normal_form a)
        _ = firstRotation ^ (a 0).val * firstReflection ^ (oddMarkerSign a).toAdd.val := by
          simp [firstRotation, firstReflection, ← map_pow, ← map_mul]
    rw [hword, map_mul, map_pow, map_pow]
    exact PairedSix2Top.mul_mem (PairedSix2Top.pow_mem hr _) (PairedSix2Top.pow_mem ht _)
  have hsecond (a : S3) : action (inl (1, a)) ∈ PairedSix2Top := by
    rw [← conjugate_first, map_mul, map_mul, map_inv]
    exact PairedSix2Top.mul_mem (PairedSix2Top.mul_mem hs (hfirst a))
      (PairedSix2Top.inv_mem hs)
  have hbase : action (inl g.left) ∈ PairedSix2Top := by
    have hsplit : (inl g.left : Wreath) = inl (g.left.1, 1) * inl (1, g.left.2) := by
      rw [← map_mul]
      simp
    rw [hsplit, map_mul]
    exact PairedSix2Top.mul_mem (hfirst g.left.1) (hsecond g.left.2)
  rw [← SemidirectProduct.inl_left_mul_inr_right g, map_mul]
  apply PairedSix2Top.mul_mem hbase
  rcases C2Wreath.cases g.right with h | h
  · rw [h, map_one, map_one]
    exact PairedSix2Top.one_mem
  · rw [h]
    exact hs

theorem range_eq : action.range = PairedSix2Top := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact action_mem g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : Wreath ≃* PairedSix2Top :=
  (MonoidHom.ofInjective action_injective).trans (MulEquiv.subgroupCongr range_eq)

end FullWreath

end PairedSixLiteralModels
end SymmetricSubgroupAsymptotics

end
