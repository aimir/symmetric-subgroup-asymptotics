import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesWreath
import Mathlib.Algebra.Group.Action.Sum

/-! Keep all other original orbit coordinates in the top of one selected
block compression.  The action on the selected blocks may be nonfaithful;
the actual embedding remains jointly faithful. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences.SelectedTop

variable {G D T I R : Type} [Group G] [Finite G] [Group D] [Finite D]
  [Group T] [Group R] [Fintype I] [Nonempty I] [MulAction T I]
  (w : G →* PermutationalWreathProduct D T I) (rest : G →* R)

/-- The full actual quotient records the selected block top and every
retained other-orbit coordinate simultaneously. -/
def projection : G →* T × R :=
  (PermutationalWreathProduct.rightHom.comp w).prod rest

abbrev Top := (projection w rest).range

instance : Finite (Top w rest) :=
  Finite.of_surjective (projection w rest).rangeRestrict
    (projection w rest).rangeRestrict_surjective

/-- The selected block action of the full retained top. -/
def selectedProjection : Top w rest →* T :=
  (MonoidHom.fst T R).comp (projection w rest).range.subtype

instance : MulAction (Top w rest) I :=
  MulAction.compHom I (selectedProjection w rest)

/-- The extra original coordinates are retained independently of the
selected block action. -/
def restProjection : Top w rest →* R :=
  (MonoidHom.snd T R).comp (projection w rest).range.subtype

/-- Enlarge the top of the original selected-orbit wreath map, keeping its
literal component coordinates. -/
def embedding : G →* PermutationalWreathProduct D (Top w rest) I where
  toFun g := ⟨(w g).left, (projection w rest).rangeRestrict g⟩
  map_one' := by
    apply PermutationalWreathProduct.ext
    · funext i
      change (w 1).left i = 1
      rw [map_one]
      rfl
    · exact (projection w rest).rangeRestrict.map_one
  map_mul' g h := by
    apply PermutationalWreathProduct.ext
    · funext i
      change (w (g * h)).left i =
        (w g).left i * (w h).left ((w g).right⁻¹ • i)
      rw [map_mul]
      rfl
    · exact (projection w rest).rangeRestrict.map_mul g h

omit [Finite G] [Finite D] [Fintype I] [Nonempty I] in
/-- Faithfulness is joint faithfulness of the selected original orbit and
all remaining original coordinates, not faithfulness of the selected top. -/
theorem embedding_injective
    (hjoint : ∀ g h : G, w g = w h → rest g = rest h → g = h) :
    Function.Injective (embedding w rest) := by
  intro g h hgh
  have hleft := congrArg (fun z : PermutationalWreathProduct D (Top w rest) I => z.left) hgh
  have htop := congrArg
    (fun z : PermutationalWreathProduct D (Top w rest) I => z.right.val) hgh
  apply hjoint g h
  · apply PermutationalWreathProduct.ext
    · exact hleft
    · exact congrArg Prod.fst htop
  · exact congrArg Prod.snd htop

omit [Finite G] [Finite D] [Fintype I] [Nonempty I] in
/-- Surjectivity of the selected original block top supplies transitivity
on the selected blocks even though other actions remain in the quotient. -/
theorem top_pretransitive
    [MulAction.IsPretransitive T I]
    (htop : Function.Surjective (PermutationalWreathProduct.rightHom.comp w)) :
    MulAction.IsPretransitive (Top w rest) I := by
  constructor
  intro i j
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq T i j
  obtain ⟨g, hg⟩ := htop t
  refine ⟨(projection w rest).rangeRestrict g, ?_⟩
  change (w g).right • i = j
  change (w g).right = t at hg
  rw [hg]
  exact ht

/-- The exact whole-source state used to compress a selected orbit. -/
def state [MulAction.IsPretransitive T I]
    (htop : Function.Surjective (PermutationalWreathProduct.rightHom.comp w))
    (hjoint : ∀ g h : G, w g = w h → rest g = rest h → g = h) :
    WreathState (Top w rest) I where
  A := G
  D := D
  groupA := inferInstance
  finiteA := inferInstance
  groupD := inferInstance
  finiteD := inferInstance
  rho := embedding w rest
  rho_injective := embedding_injective w rest hjoint
  top_surjective := (projection w rest).rangeRestrict_surjective
  top_pretransitive := top_pretransitive w rest htop

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences.SelectedTop
