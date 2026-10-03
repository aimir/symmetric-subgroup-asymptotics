import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixNormalComparatorSource
import SymmetricSubgroupAsymptotics.OddMarker

/-!
# The degree-six `S₃ ≀ C₂` affine cell

Coordinatewise sign on the two `S₃` factors, together with the unchanged
block swap, gives an onto map

`S₃ ≀ C₂ → C₂ ≀ C₂ = D₈`.

Its kernel is `A₃²`.  It is contained in every nontrivial normal subgroup,
so the nonbottom axes use the faithful degree-four action of `D₈`.  The
bottom axis uses the ternary cyclic dual on the second derived subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeSixS3Wreath

private abbrev S3 := Equiv.Perm (Fin 3)
private abbrev C2 := Multiplicative (ZMod 2)

/-- The exact full two-block wreath target. -/
abbrev G := C2Wreath.W S3

/-- Its sign quotient, the dihedral group of order eight. -/
abbrev D8 := C2Wreath.W C2

def signBase : S3 × S3 →* C2 × C2 :=
  oddMarkerSign.prodMap oddMarkerSign

private theorem signBase_swap_compatible (g : C2) :
    signBase.comp (C2Wreath.swapAut S3 g).toMonoidHom =
      (C2Wreath.swapAut C2 g).toMonoidHom.comp signBase := by
  apply MonoidHom.ext
  intro x
  rcases C2Wreath.cases g with rfl | rfl
  · simp [signBase, C2Wreath.swapAut_one]
  · simp [signBase, C2Wreath.swapAut_gen]

/-- Coordinatewise sign and the unchanged block swap. -/
def projection : G →* D8 :=
  SemidirectProduct.map signBase (MonoidHom.id C2) signBase_swap_compatible

theorem projection_surjective : Function.Surjective projection := by
  intro y
  obtain ⟨a, ha⟩ := oddMarkerSign_surjective y.left.1
  obtain ⟨b, hb⟩ := oddMarkerSign_surjective y.left.2
  refine ⟨⟨(a, b), y.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · exact Prod.ext ha hb
  · rfl

private abbrev PairPoint := Fin 1 ⊕ Fin 1

/-- The regular two-point action of the base `C₂`. -/
def c2Action : C2 →* Equiv.Perm PairPoint :=
  C2Wreath.blockSwap (Fin 1)

theorem c2Action_injective : Function.Injective c2Action := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rcases C2Wreath.cases x with h | h
  · exact h
  · exfalso
    rw [h, c2Action, C2Wreath.blockSwap] at hx
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, C2Wreath.gen_ne_one,
      if_false] at hx
    have := congrArg (fun sigma : Equiv.Perm PairPoint => sigma (Sum.inl 0)) hx
    simp at this

/-- Flatten the two binary blocks to four points. -/
def d8PointEquiv : PairPoint ⊕ PairPoint ≃ Fin 4 :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

/-- The faithful imprimitive four-point action of `D₈`. -/
def d8Action : D8 →* Equiv.Perm (Fin 4) :=
  d8PointEquiv.permCongrHom.toMonoidHom.comp
    (C2Wreath.action c2Action)

theorem d8Action_injective : Function.Injective d8Action :=
  d8PointEquiv.permCongrHom.injective.comp
    (C2Wreath.action_injective c2Action c2Action_injective)

/-- The two exact finite group facts left after defining the sign quotient. -/
structure Algebra : Type where
  target : DerivedHead.DerivedCyclicTarget G projection.ker 1 3
  normal_cover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → projection.ker ≤ N

theorem card_G : Nat.card G = 72 := by
  rw [SemidirectProduct.card, Nat.card_prod, Nat.card_perm, Nat.card_fin]
  norm_num

theorem automorphism_card_le : Nat.card (G ≃* G) ≤ 2 ^ 216 := by
  calc
    Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.log 2 (Nat.card G) :=
      Non2UnipotentPrefixFiniteMenu.mulEquiv_card_le_card_pow_log G
    _ = 72 ^ 6 := by rw [card_G]; norm_num
    _ ≤ 2 ^ 216 := by norm_num

end DegreeSixS3Wreath

namespace Non2UnipotentPrefixFiniteMenu

/-- Recognition data for the literal retained wreath action. -/
structure PreE7DegreeSixS3WreathSource
    (U : PreE7NonPairActionClass 6) : Type where
  equiv : preE7NonPairAction 6 U ≃* DegreeSixS3Wreath.G

namespace PreE7DegreeSixS3WreathSource

variable {U : PreE7NonPairActionClass 6}
  (S : PreE7DegreeSixS3WreathSource U)
  (A : DegreeSixS3Wreath.Algebra)

/-- The exact normal-comparator model with `D₈` comparator. -/
def model : PreE7NormalComparatorModel 6 U where
  G := DegreeSixS3Wreath.G
  equiv := S.equiv
  index := Unit
  R := DegreeSixS3Wreath.D8
  degree := 4
  action := DegreeSixS3Wreath.d8Action
  action_injective := DegreeSixS3Wreath.d8Action_injective
  proj := fun _ => DegreeSixS3Wreath.projection
  proj_surjective := fun _ => DegreeSixS3Wreath.projection_surjective
  normal_cover := fun N hN hNb => ⟨(), A.normal_cover N hN hNb⟩
  tailSlope := Real.logb 2 3 / 3
  tailConstant := Nat.card
    (DegreeSixS3Wreath.G ≃* DegreeSixS3Wreath.G)
  tailConstant_nonneg := by positivity
  tail := fun _ J => A.target.epi_card_le_ternary J
  comparator_window := by
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := logThreeThird_le_window (by norm_num)

private theorem tailConstant_le :
    (S.model A).tailConstant ≤ (2 : ℝ) ^ (36 * (6 : ℝ)) := by
  change (Nat.card (DegreeSixS3Wreath.G ≃* DegreeSixS3Wreath.G) : ℝ) ≤ _
  calc
    (Nat.card (DegreeSixS3Wreath.G ≃* DegreeSixS3Wreath.G) : ℝ) ≤
        ((2 ^ 216 : ℕ) : ℝ) := by
      exact_mod_cast DegreeSixS3Wreath.automorphism_card_le
    _ = (2 : ℝ) ^ (36 * (6 : ℝ)) := by norm_num

/-- Completed degree-six source for the full wreath cell. -/
noncomputable def source : PreE7RankTailSourceOrYonedaTopData 6 U :=
  DegreeSixNormalComparatorSource.source (S.model A) (S.tailConstant_le A)

end PreE7DegreeSixS3WreathSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
