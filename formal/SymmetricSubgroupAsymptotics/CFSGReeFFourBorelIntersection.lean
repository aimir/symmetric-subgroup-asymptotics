import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleParabolic
import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedOppositeSylow

/-! The retained diagonal in the original exceptional-fixed group is the
intersection of its two actual Sylow normalizers. A positive element
normalizing the opposite Sylow is trivial, so the proved U-D Borel
factorization suffices. No new torus identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBorelIntersection
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedPositiveSylow
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourOriginalMiddleParabolic
open CFSGReeFFourDerivedOppositeSylow CFSGFFourOriginalMiddleWords
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckNormalizerEnvelope
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem fixedBorel_eq_positive_normalizer (m : ℕ) :
    fixedBorel m=Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m)) :=
  le_antisymm (fixedBorel_le_normalizer m) (normalizer_positive_le_borel m)

private theorem diagonal_le_negative_normalizer (m : ℕ) :
    fixedDiagonal m≤Subgroup.normalizer (fixedNegative m : Set (originalModelFixed m)) := by
  intro d hdD
  have hraw : rawHom (Field m) d.val∈diagonalNormalizer (Field m) := hdD
  change d∈Subgroup.normalizer
    ((Negative (Field m)).comap (fixedRawHom m) : Set (originalModelFixed m))
  exact Subgroup.le_normalizer_comap (fixedRawHom m) hraw.1.2

private theorem positive_inf_negative_normalizer (m : ℕ) :
    fixedPositive m⊓Subgroup.normalizer (fixedNegative m : Set (originalModelFixed m))=⊥ := by
  let e := MulAut.conj (oppositionFixed m)
  let Q : Sylow 2 (originalModelFixed m) :=
    (fixedPositiveSylow m).mapSurjective (f:=e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup (originalModelFixed m))=fixedNegative m := by
    change (fixedPositiveSylow m : Subgroup (originalModelFixed m)).map e.toMonoidHom=_
    rw [fixedPositiveSylow_coe]
    exact fixed_positive_image_eq_fixed_negative m
  have hP : IsPGroup 2 (fixedPositive m) :=
    fixedPositiveSylow_coe m ▸ (fixedPositiveSylow m).isPGroup'
  have he : fixedPositive m⊓Subgroup.normalizer
      ((Q : Subgroup (originalModelFixed m)) : Set (originalModelFixed m))=
        fixedPositive m⊓(Q : Subgroup (originalModelFixed m)) :=
    hP.inf_normalizer_sylow Q
  rw [hQ] at he
  exact he.trans (fixed_positive_inf_negative m)

theorem fixedDiagonal_eq_pairNormalizer (m : ℕ) :
    fixedDiagonal m=Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m))⊓
      Subgroup.normalizer (fixedNegative m : Set (originalModelFixed m)) := by
  apply le_antisymm
  · exact le_inf ((diagonal_le_borel m).trans (fixedBorel_le_normalizer m))
      (diagonal_le_negative_normalizer m)
  · intro g hg
    have hgB := normalizer_positive_le_borel m hg.1
    obtain ⟨u,hu,d,hdD,he⟩ := exists_fixed_borel_factors m ⟨g,hgB⟩
    change g=u*d at he
    let N := Subgroup.normalizer (fixedNegative m : Set (originalModelFixed m))
    have huN : u∈N := by
      have hh := N.mul_mem hg.2 (N.inv_mem (diagonal_le_negative_normalizer m hdD))
      rw [he,mul_inv_cancel_right] at hh
      exact hh
    have hu1 : u=1 := by
      have hh : u∈fixedPositive m⊓N := ⟨hu,huN⟩
      rw [positive_inf_negative_normalizer,Subgroup.mem_bot] at hh
      exact hh
    rw [hu1,one_mul] at he
    rw [he]
    exact hdD

def oppositeBorel (m : ℕ) : Subgroup (originalModelFixed m) :=
  Subgroup.normalizer (fixedNegative m : Set (originalModelFixed m))

theorem fixedBorel_opposition_map (m : ℕ) :
    (fixedBorel m).map (MulAut.conj (oppositionFixed m)).toMonoidHom=oppositeBorel m := by
  rw [fixedBorel_eq_positive_normalizer]
  exact (Subgroup.map_equiv_normalizer_eq (fixedPositive m) (MulAut.conj (oppositionFixed m))).trans
    (congrArg (fun P : Subgroup (originalModelFixed m)=>
      Subgroup.normalizer (P : Set (originalModelFixed m)))
      (fixed_positive_image_eq_fixed_negative m))

theorem fixedDiagonal_eq_borel_inf_opposite (m : ℕ) :
    fixedDiagonal m=fixedBorel m⊓oppositeBorel m := by
  rw [fixedBorel_eq_positive_normalizer]
  exact fixedDiagonal_eq_pairNormalizer m

end SymmetricSubgroupAsymptotics.CFSGReeFFourBorelIntersection
