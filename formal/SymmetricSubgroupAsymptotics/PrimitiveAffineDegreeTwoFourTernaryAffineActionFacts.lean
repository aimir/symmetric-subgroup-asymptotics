import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernarySemidirectBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryAffineModel

/-!
# Small action kernels and the literal ternary block orbits

The action-kernel bound tests the four projected coordinate columns. A
single nonvanishing translation vector supplies each ternary block orbit,
and explicit Klein coordinates move between the four blocks. Together with
the exact semidirect equivalence, these certify all eight original tops.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoFourTernaryAffineActionFacts

open TernarySignedBlockCoordinates
open PrimitiveAffineDegreeTwoFourTernaryCoordinates
open PrimitiveAffineDegreeTwoFourTernaryBinaryCoordinates
open PrimitiveAffineDegreeTwoFourTernaryCoreCoordinates
open PrimitiveAffineDegreeTwoFourTernarySemidirectBinding
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def fixedColumns (r : Fin 8) (q : Frame) : Prop :=
  ∀ i : Fin 4, linear (toSigned q) (projection r (Pi.single i 1)) =
    projection r (Pi.single i 1)

instance (r : Fin 8) (q : Frame) : Decidable (fixedColumns r q) :=
  inferInstanceAs (Decidable (∀ i : Fin 4,
    linear (toSigned q) (projection r (Pi.single i 1)) = projection r (Pi.single i 1)))

def KernelCoordinates (r : Fin 8) :=
  {q : Frame // allowed (shape r) q ∧ fixedColumns r q}

instance (r : Fin 8) : Fintype (KernelCoordinates r) := inferInstanceAs
  (Fintype {q : Frame // allowed (shape r) q ∧ fixedColumns r q})

def kernelCoordinate (r : Fin 8) (g : (coreAction r).ker) : KernelCoordinates r :=
  ⟨g.val.val, g.val.property, by
    intro i
    have he : coreAction r g.val = 1 := g.property
    exact congrArg (fun f : MulAut (Multiplicative (Core r)) =>
      (f (Multiplicative.ofAdd
        ⟨projection r (Pi.single i 1), projection_mem r _⟩)).toAdd.val) he⟩

theorem kernelCoordinate_injective (r : Fin 8) : Function.Injective (kernelCoordinate r) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : KernelCoordinates r => q.val) he

theorem kernelCoordinates_card_le_two (r : Fin 8) : Nat.card (KernelCoordinates r) ≤ 2 := by
  rw [Nat.card_eq_fintype_card]
  fin_cases r <;> decide +kernel

theorem coreAction_kernel_card_le_two (r : Fin 8) : Nat.card (coreAction r).ker ≤ 2 :=
  (Nat.card_le_card_of_injective (kernelCoordinate r) (kernelCoordinate_injective r)).trans
    (kernelCoordinates_card_le_two r)

def blockCoordinate : Fin 4 → Klein :=
  ![Multiplicative.ofAdd (0, 0), Multiplicative.ofAdd (1, 0),
    Multiplicative.ofAdd (0, 1), Multiplicative.ofAdd (1, 1)]

def moveFrame (r : Fin 8) (i j : Fin 4) : Frame :=
  let d := blockCoordinate j * (blockCoordinate i)⁻¹
  let c := d.toAdd.1 + d.toAdd.2
  ⟨if r = 5 then (fun k => Multiplicative.ofAdd (![0, c, c, 0] k)) else 1, d⟩

theorem moveFrame_mem (r : Fin 8) (i j : Fin 4) : moveFrame r i j ∈ Complement r := by
  fin_cases r <;> revert i j <;> decide +kernel

def blockMove (r : Fin 8) (i j : Fin 4) : Complement r :=
  ⟨moveFrame r i j, moveFrame_mem r i j⟩

theorem blockMove_apply (r : Fin 8) (i j : Fin 4) :
    (toSigned (blockMove r i j).val).right i = j := by
  fin_cases r <;> revert i j <;> decide +kernel

/-- This vector belongs to all three core spaces and is nonzero in every coordinate. -/
def commonVector : Vector := ![1, 2, 1, 2]

def fillVector (i : Fin 4) (z : Scalar) : Vector :=
  ((commonVector i)⁻¹ * z) • commonVector

theorem fillVector_mem (r : Fin 8) (i : Fin 4) (z : Scalar) : fillVector i z ∈ Core r := by
  change projection r (fillVector i z) = fillVector i z
  funext j
  fin_cases r <;> revert i z j <;> decide +kernel

theorem fillVector_apply (i : Fin 4) (z : Scalar) : fillVector i z i = z := by
  revert i z
  decide +kernel

def fillCore (r : Fin 8) (i : Fin 4) (z : Scalar) : Core r :=
  ⟨fillVector i z, fillVector_mem r i z⟩

theorem chart_model_apply (r : Fin 8) (g : Model r) (x : Fin 12) :
    pointChart (phase r) ((modelOriginalEquiv r g : Equiv.Perm (Fin 12)) x) =
      action (modelInclusion r g) (pointChart (phase r) x) := by
  rw [modelOriginalEquiv_apply]
  change pointChart (phase r) ((pointChart (phase r)).symm
    (action (modelInclusion r g) (pointChart (phase r) x))) = _
  exact (pointChart (phase r)).apply_symm_apply _

theorem chart_translation_apply (r : Fin 8) (v : Multiplicative (Core r)) (x : Fin 12) :
    pointChart (phase r)
      ((modelOriginalEquiv r (SemidirectProduct.inl v) : Equiv.Perm (Fin 12)) x) =
      (v.toAdd.val (pointChart (phase r) x).2 + (pointChart (phase r) x).1,
        (pointChart (phase r) x).2) := by
  rw [chart_model_apply]
  change (v.toAdd.val (pointChart (phase r) x).2 +
    (1 : Scalar) * (pointChart (phase r) x).1, (pointChart (phase r) x).2) = _
  rw [one_mul]

theorem same_block_iff_translation (r : Fin 8) (x y : Fin 12) :
    degreeTwoFourTernaryBlock x = degreeTwoFourTernaryBlock y ↔
      ∃ v : Multiplicative (Core r),
        ((affineEquiv r).symm (SemidirectProduct.inl v) : Equiv.Perm (Fin 12)) x = y := by
  constructor
  · intro hxy
    have hb : (pointChart (phase r) x).2 = (pointChart (phase r) y).2 := by
      simpa only [chart_block] using hxy
    let v := fillCore r (pointChart (phase r) x).2
      ((pointChart (phase r) y).1 - (pointChart (phase r) x).1)
    refine ⟨Multiplicative.ofAdd v, ?_⟩
    apply (pointChart (phase r)).injective
    rw [show (affineEquiv r).symm = modelOriginalEquiv r from rfl,
      chart_translation_apply]
    apply Prod.ext
    · change fillVector (pointChart (phase r) x).2
        ((pointChart (phase r) y).1 - (pointChart (phase r) x).1)
        (pointChart (phase r) x).2 + (pointChart (phase r) x).1 = _
      rw [fillVector_apply, sub_add_cancel]
    · exact hb
  · rintro ⟨v, hv⟩
    have h := congrArg (fun z : Fin 12 => (pointChart (phase r) z).2) hv
    change (pointChart (phase r)
      ((modelOriginalEquiv r (SemidirectProduct.inl v) : Equiv.Perm (Fin 12)) x)).2 =
      (pointChart (phase r) y).2 at h
    rw [chart_translation_apply] at h
    simpa only [chart_block] using h

theorem original_transitive (r : Fin 8) :
    MulAction.IsPretransitive (degreeTwoFourTernaryInterface r).top (Fin 12) := by
  constructor
  intro x y
  let px := pointChart (phase r) x
  let py := pointChart (phase r) y
  let q := blockMove r px.2 py.2
  let c : Scalar := (toSigned q.val).left py.2
  let v := fillCore r py.2 (py.1 - c * px.1)
  refine ⟨modelOriginalEquiv r ⟨Multiplicative.ofAdd v, q⟩, ?_⟩
  apply (pointChart (phase r)).injective
  change pointChart (phase r)
    ((modelOriginalEquiv r ⟨Multiplicative.ofAdd v, q⟩ : Equiv.Perm (Fin 12)) x) =
      pointChart (phase r) y
  rw [chart_model_apply]
  change (v.val ((toSigned q.val).right px.2) +
      ((toSigned q.val).left ((toSigned q.val).right px.2) : Scalar) * px.1,
      (toSigned q.val).right px.2) = py
  rw [blockMove_apply]
  apply Prod.ext
  · change fillVector py.2 (py.1 - c * px.1) py.2 + c * px.1 = py.1
    rw [fillVector_apply, sub_add_cancel]
  · rfl

/-- The eight structures are now assembled from their actual literal affine models. -/
noncomputable def topStructure (r : Fin 8) :
    DegreeTwoFourTernaryTopStructure (degreeTwoFourTernaryInterface r) :=
  degreeTwoFourTernaryTopStructureOfAffine _ (affineEquiv r)
    (core_exponent_three r) (core_card_lower r) (complement_binary r)
    (coreAction_kernel_card_le_two r) (original_transitive r)
    (same_block_iff_translation r)

end PrimitiveAffineDegreeTwoFourTernaryAffineActionFacts
end SymmetricSubgroupAsymptotics

end
