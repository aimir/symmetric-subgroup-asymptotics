import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockDistinctSignIrreducible
import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationSubmoduleDiagonalAction

/-!
# Faithfulness in the four-distinct-sign branch

Once the correlated ternary layer is the full four-coordinate product, an
element acting trivially on it cannot move a block: a vector supported in
one coordinate detects that movement.  After the block top is killed, each
local complement coordinate is detected by the faithful one-dimensional
local representation.  The literal quotient wreath embedding then detects
the original quotient element.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private theorem degreeThreeFourBlockTranslationCoordinateEquiv_apply
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4)
    (x : TranslationSubmodule block P) (i : Fin 4) :
    degreeThreeFourBlockTranslationCoordinateEquiv
        block P hr hs hcomponent hbinary hfour x i =
      x.1 ((degreeThreeFourBlockIndexEquiv block hs).symm i) :=
  rfl

/-- The actual quotient conjugation representation is faithful in the
four-distinct-sign branch. -/
theorem degreeThreeFourBlock_quotientRepresentation_injective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    Function.Injective
      (elementaryChart block P).quotientRepresentation.ρ := by
  let e := degreeThreeFourBlockIndexEquiv block hs
  let coordinates := degreeThreeFourBlockTranslationCoordinateEquiv
    block P hr hs hcomponent hbinary hfour
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (E block P) q
  have hfix : ∀ x : TranslationSubmodule block P,
      (elementaryChart block P).quotientRepresentation.ρ
        (QuotientGroup.mk' (E block P) a) x = x := by
    intro x
    have hx := DFunLike.congr_fun hq x
    simpa only [one_apply] using hx
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    have hdim' := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at hdim'
    exact hdim'
  letI : Fact P.p.Prime := (chart block P).primeFact
  letI : Nontrivial (chart block P).V :=
    Module.nontrivial_of_finrank_pos (R := ZMod P.p) (by
      rw [hdim]
      decide)
  obtain ⟨z, hz⟩ := exists_ne (0 : (chart block P).V)
  have htop : (ambientEmbedding block a).right = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_contra hi
    let y : Fin 4 → (chart block P).V :=
      fun j ↦ if j = e i then z else 0
    let x : TranslationSubmodule block P := coordinates.symm y
    have hcoordinates : coordinates x = y := coordinates.apply_symm_apply y
    have hxi : x.1 i ≠ 0 := by
      have hvalue : x.1 i = z := by
        have h := congrFun hcoordinates (e i)
        rw [degreeThreeFourBlockTranslationCoordinateEquiv_apply,
          e.symm_apply_apply] at h
        simpa only [y, if_pos rfl] using h
      rw [hvalue]
      exact hz
    have htarget := translationSubmodule_coordinate_ne_zero_of_transport
      block P a x i hxi
    rw [hfix x] at htarget
    have hvalue := congrFun hcoordinates
      (e ((ambientEmbedding block a).right • i))
    rw [degreeThreeFourBlockTranslationCoordinateEquiv_apply,
      e.symm_apply_apply] at hvalue
    have hoff : e ((ambientEmbedding block a).right • i) ≠ e i :=
      fun h ↦ hi (e.injective h)
    have hzero : x.1 ((ambientEmbedding block a).right • i) = 0 := by
      rw [hvalue]
      simp only [y, if_neg hoff]
    exact htarget hzero
  have hlocal : ∀ i : block.Points,
      localMap block P ((ambientEmbedding block a).left i) = 1 := by
    intro i
    apply binaryAffineLocalLinearRepresentation_injective block P
    apply LinearMap.ext
    intro v
    let y : Fin 4 → (chart block P).V :=
      fun j ↦ if j = e i then v else 0
    let x : TranslationSubmodule block P := coordinates.symm y
    have hcoordinates : coordinates x = y := coordinates.apply_symm_apply y
    have hxi : x.1 i = v := by
      have hvalue := congrFun hcoordinates (e i)
      rw [degreeThreeFourBlockTranslationCoordinateEquiv_apply,
        e.symm_apply_apply] at hvalue
      simpa only [y, if_pos rfl] using hvalue
    have hcoordinate :=
      translationSubmodule_quotientRepresentation_coordinate
        block P a htop x i
    rw [hfix x, hxi] at hcoordinate
    simpa only [map_one, one_apply] using hcoordinate.symm
  apply quotientEmbedding_injective block P
  rw [quotientEmbedding,
    PermutationalWreathProduct.Compression.quotientEmbedding]
  simp only [map_one]
  change PermutationalWreathProduct.Compression.map
      (ambientEmbedding block) (localMap block P) a = 1
  apply PermutationalWreathProduct.ext
  · funext i
    change localMap block P ((ambientEmbedding block a).left i) = 1
    exact hlocal i
  · change (ambientEmbedding block a).right = 1
    exact htop

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
