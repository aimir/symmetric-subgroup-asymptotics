import SymmetricSubgroupAsymptotics.NormalizerSharedOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators

/-! An actual full coordinate axis and an actual coordinate-swapping
conjugator pay the ordinary rank of ONE local factor above the original
normal quotient. The normalizer condition is proved inside the SAME
normal subgroup. No normal-generation-to-ordinary shortcut is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwoCoordinateAxisOrdinaryGenerators

theorem genRank_le_local_add_quotient
    {G L : Type} [Group G] [Finite G] [Group L] [Finite L]
    (N : Subgroup G) [N.Normal] (f g : N →* L)
    (hjoint : Function.Injective (fun x : N => (f x,g x)))
    (haxis : Function.Surjective (f.comp g.ker.subtype))
    (h : G) (alpha : MulAut L)
    (hconj : ∀ x : N, f ((MulAut.conjNormal h) x) = alpha (g x)) :
    MarkedC4.genRank G ≤ MarkedC4.genRank L + MarkedC4.genRank (G ⧸ N) := by
  let A : Subgroup G := g.ker.map N.subtype
  have hAN : A ≤ N := by
    rintro z ⟨x,hx,rfl⟩
    exact x.property
  have hnorm : N ≤ Subgroup.normalizer A := by
    have hh := g.ker.le_normalizer_map N.subtype
    intro z hz
    apply hh
    refine ⟨⟨z,hz⟩,?_,rfl⟩
    rw [Subgroup.normalizer_eq_top]
    trivial
  let M : Subgroup G := Subgroup.normalClosure (A : Set G)
  have hcl : M = N := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal hAN
    · intro z hz
      let zN : N := ⟨z,hz⟩
      obtain ⟨a,ha⟩ := haxis (f zN)
      have ha' : f (a : N) = f zN := ha
      have haM : (((a : N) : G)) ∈ M :=
        Subgroup.subset_normalClosure ⟨(a : N),a.property,rfl⟩
      let r : N := zN*(a : N)⁻¹
      have hfr : f r = 1 := by
        change f (zN*(a : N)⁻¹) = 1
        rw [map_mul,map_inv,ha',mul_inv_cancel]
      let x : N := (MulAut.conjNormal h).symm r
      have hcx : (MulAut.conjNormal h) x = r := (MulAut.conjNormal h).apply_symm_apply r
      have hgx : g x = 1 := by
        apply alpha.injective
        rw [←hconj,hcx,hfr,map_one]
      have hxA : (x : G) ∈ A := ⟨x,hgx,rfl⟩
      have hxM : (x : G) ∈ M := Subgroup.subset_normalClosure hxA
      have hrM : (r : G) ∈ M := by
        have hh := (inferInstance : M.Normal).conj_mem (x : G) hxM h
        have he : h*(x : G)*h⁻¹ = (r : G) := congrArg Subtype.val hcx
        rwa [he] at hh
      have heN : r*(a : N) = zN := by dsimp only [r]; group
      have heG : (r : G)*((a : N) : G) = z := congrArg Subtype.val heN
      exact heG ▸ M.mul_mem hrM haM
  have hfA : Function.Injective (f.comp g.ker.subtype) := by
    intro a b he
    apply Subtype.ext
    apply hjoint
    apply Prod.ext
    · exact he
    · exact a.property.trans b.property.symm
  let e : A ≃* L :=
    (g.ker.equivMapOfInjective N.subtype N.subtype_injective).symm.trans
      (MulEquiv.ofBijective (f.comp g.ker.subtype) ⟨hfA,haxis⟩)
  have hgen := NormalizerSharedOrdinaryGenerators.genRank_le N A hnorm hcl
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e] at hgen
  exact hgen

end SymmetricSubgroupAsymptotics.TwoCoordinateAxisOrdinaryGenerators
