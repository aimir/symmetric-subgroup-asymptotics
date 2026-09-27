import SymmetricSubgroupAsymptotics.DegreeTwentySevenClosure
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import SymmetricSubgroupAsymptotics.OutsideOrbitDegreeThree
import SymmetricSubgroupAsymptotics.TernaryHighImprimitiveDegrees

/-!
# Structural closure of the degree-nine ternary endpoint

A transitive three-point top with a nonzero relative ternary head is the
cyclic group of order three: the full symmetric group kills every invariant
ternary character by inversion.  Applying this fact to the literal minimal
three-by-three block system removes the former finite degree-nine order
premise.  The same simultaneous fibre-sign fork used at degree twenty seven
then puts every degree-nine rank-two pair in the existing 3-group owner.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem finThree_exists_conjugate_inverse (s : Equiv.Perm (Fin 3)) :
    ∃ g : Equiv.Perm (Fin 3), g * s * g⁻¹ = s⁻¹ := by
  decide +kernel +revert

/-- If a three-point permutation subgroup is the whole symmetric group,
ambient inversion annihilates the relative ternary head of every normal
subgroup. -/
theorem degreeThree_top_relativeHead_eq_zero
    (U : Subgroup (Equiv.Perm (Fin 3))) (hU : U = ⊤)
    (M : Subgroup U) [M.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) = 0 := by
  letI : Subsingleton (primeRelativeCharacters 3 M) := ⟨by
    intro χ ψ
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro a
    let m : M := a.toMul
    change χ.1 (Additive.ofMul m) = ψ.1 (Additive.ofMul m)
    have character_zero : ∀ θ : primeRelativeCharacters 3 M,
        θ.1 (Additive.ofMul m) = 0 := by
      intro θ
      obtain ⟨g₀, hg₀⟩ :=
        finThree_exists_conjugate_inverse ((m : M) : Equiv.Perm (Fin 3))
      let g : U := ⟨g₀, by rw [hU]; exact Subgroup.mem_top g₀⟩
      have hg : g * (m : U) * g⁻¹ = (m : U)⁻¹ := by
        apply Subtype.ext
        exact hg₀
      have hθ := θ.2 g m
      have hconj :
          (⟨g * (m : U) * g⁻¹,
            Subgroup.Normal.conj_mem inferInstance (m : U) m.2 g⟩ : M) = m⁻¹ := by
        apply Subtype.ext
        exact hg
      rw [hconj] at hθ
      change θ.1 (-Additive.ofMul m) = θ.1 (Additive.ofMul m) at hθ
      rw [map_neg] at hθ
      let x : ZMod 3 := θ.1 (Additive.ofMul m)
      have htwo : (2 : ZMod 3) * x = 0 := by
        calc
          (2 : ZMod 3) * x = x + x := by ring
          _ = x + -x := by rw [hθ]
          _ = 0 := add_neg_cancel x
      exact (mul_eq_zero.mp htwo).resolve_left (by decide)
    rw [character_zero χ, character_zero ψ]⟩
  exact Module.finrank_zero_of_subsingleton

/-- A transitive three-point permutation group carrying a rank-one relative
ternary normal pair is the cyclic group of order three. -/
theorem degreeThreePermutation_rankOne_isPGroup
    (U : Subgroup (Equiv.Perm (Fin 3)))
    [MulAction.IsPretransitive U (Fin 3)]
    (M : Subgroup U) [M.Normal]
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) = 1) :
    IsPGroup 3 U := by
  by_cases htop : U = ⊤
  · have hzero := degreeThree_top_relativeHead_eq_zero U htop M
    omega
  · have htrans : PermutationSubgroupTransitive U := by
      intro x y
      obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U x y
      exact ⟨u, u.2, hu⟩
    have hU :=
      RepeatedMarkerOwnerBound.transitive_proper_degreeThree_eq_alternating
        U htrans htop
    have hcard : Nat.card U = 3 := by
      rw [hU, nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card]
    exact IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hcard)

/-- Abstract faithful-action form of the three-point structural result. -/
theorem degreeThree_rankOne_isPGroup
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] [Nonempty X]
    (hDegree : Nat.card X = 3)
    (M : Subgroup G) [M.Normal]
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) = 1) :
    IsPGroup 3 G := by
  let e : X ≃ Fin 3 := Finite.equivFinOfCardEq hDegree
  let U := labelledActionImage (A := G) e
  let T := labelledActionNormal e M
  letI : MulAction.IsPretransitive U (Fin 3) :=
    (labelledAction_pretransitive_iff e).mp inferInstance
  have hTRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 T) = 1 := by
    rw [← labelledActionNormal_head e 3 M]
    exact hRank
  have hU : IsPGroup 3 U := degreeThreePermutation_rankOne_isPGroup U T hTRank
  exact hU.of_equiv (faithfulLabelledActionEquiv e).symm

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- The rank-two degree-nine endpoint fixes a literal three-by-three minimal
block system and a rank-one original normal top image. -/
theorem degreeNine_minimalBlock_data
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 9)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) :
    Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 3 ∧
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1 := by
  letI : Nonempty Ω := ⟨ω₀⟩
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  let T := originalNormalRange D.topMap N
  let t := Module.finrank (ZMod 3) (primeRelativeCharacters 3 T)
  have hr : 2 ≤ r := by simpa only [r] using D.degrees_ge_two.1
  have hs : 2 ≤ s := by simpa only [s] using D.degrees_ge_two.2
  have hrs : r * s = 9 := by
    have hproduct : r * s = Nat.card Ω := by
      simpa only [r, s] using D.degree_product
    exact hproduct.trans hDegree
  have hr3 : r = 3 := by
    have hrdiv : r ∣ 9 := ⟨s, hrs.symm⟩
    have hrle : r ≤ 9 := Nat.le_of_dvd (by decide) hrdiv
    interval_cases r <;> norm_num at hrs ⊢ <;> omega
  have hs3 : s = 3 := by
    have hrs' : 3 * s = 9 := by simpa only [hr3] using hrs
    omega
  letI : Nontrivial D.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by simpa only [r] using hr)
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
  obtain ⟨c, hc⟩ := hChief D.Component D.Fibre
  let v := actualChiefSeriesTernaryWeight c
  have hv : v ≤ 1 := by
    have hv' : v ≤ r / 3 := by simpa only [v, r] using hc
    simpa only [hr3] using hv'
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  have ht : t ≤ 1 := by
    have ht' := transitiveTernaryHead_stability hChief hPrimitive h18
      (A := D.Top) (Ω := D.Points) T
    simpa only [t, s, hs3, ternaryStabilityBound_three] using ht'
  have hd := D.head_bound_nat N c
  have hd' : 2 ≤ v + t := by
    rw [hRank] at hd
    simpa only [s, hs3, ternaryIndexWidth_three, mul_one, v, t, T] using hd
  have htExact : t = 1 := by omega
  exact ⟨by simpa only [r] using hr3,
    by simpa only [s] using hs3,
    by simpa only [t, T] using htExact⟩

include D in
/-- Every degree-nine rank-two normal pair enters the existing transitive
3-group owner.  No finite action catalogue or group-order premise is used. -/
theorem degreeNine_rankTwo_isPGroup
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 9)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) :
    IsPGroup 3 A := by
  obtain ⟨hFibre, hPoints, hTop⟩ := D.degreeNine_minimalBlock_data
    hChief hPrimitive h18 N hDegree hRank
  letI : Fintype D.Points := Fintype.ofFinite _
  letI (x : D.Points) : Fintype (originalBlockFibre D.map x) :=
    Fintype.ofFinite _
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  let T := originalNormalRange D.topMap N
  have hTopGroup : IsPGroup 3 D.Top :=
    degreeThree_rankOne_isPGroup hPoints T (by simpa only [T] using hTop)
  let e := D.ternaryFibreCharts hFibre
  by_cases hSigns :
      DegreeThreeBlockInversionHead.coordinateSigns D.map D.map_equivariant = 1
  · exact DegreeThreeBlockInversionHead.originalGroup_isPGroup_of_coordinateSigns_eq_one
      (hb := D.map_equivariant) D.map e hTopGroup hSigns
  · have hexists : ∃ x : D.Points,
        OriginalBlockSignCoordinates.coordinateSign D.map D.map_equivariant x ≠ 1 := by
      by_contra h
      simp only [not_exists, not_ne_iff] at h
      apply hSigns
      apply MonoidHom.ext
      intro k
      funext x
      simpa only [DegreeThreeBlockInversionHead.coordinateSigns,
        MonoidHom.one_apply] using DFunLike.congr_fun (h x) k
    obtain ⟨x₀, hx₀⟩ := hexists
    have hle :=
      DegreeThreeBlockInversionHead.originalNormal_primeRelativeHead_le_top
        (hb := D.map_equivariant) D.map N e x₀ hx₀
    rw [hRank, hTop] at hle
    omega

end OriginalMinimalBlock

/-- The minimal block is selected internally from an arbitrary original
degree-nine action. -/
theorem degreeNine_rankTwo_isPGroup
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 9)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2) :
    IsPGroup 3 A := by
  have hTwo : 2 ≤ Nat.card Ω := by omega
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hTwo
  have himprimitive : ¬ MulAction.IsPreprimitive A Ω := by
    intro hp
    letI : MulAction.IsPreprimitive A Ω := hp
    have hsafe := hPrimitive A Ω (by omega) (by omega) (by omega) N
    omega
  let ω₀ : Ω := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := A) ω₀ :=
    Classical.choice (originalMinimalBlock_nonempty ω₀ himprimitive)
  exact D.degreeNine_rankTwo_isPGroup
    hChief hPrimitive h18 N hDegree hRank

end SymmetricSubgroupAsymptotics

end
