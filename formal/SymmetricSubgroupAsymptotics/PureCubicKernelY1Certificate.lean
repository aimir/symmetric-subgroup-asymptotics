import SymmetricSubgroupAsymptotics.CubicKernelNonzeroHead
import SymmetricSubgroupAsymptotics.CubicKernelCoordinateEnvelope
import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailSource
import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators

/-! A pure repeated scalar C3 kernel has a Y1 quotient certificate.
Surviving scalar rows use the existing headed count with weight2; if all
scalar rows vanish the actual top is an isomorphism with C3. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PureCubicKernelY1Certificate
open Non2UnipotentPrefixFiniteMenu CubicElementaryKernelCoordinates

private theorem known_slope : Real.logb 2 (38 / 25) ≤ (153 : ℝ)/200 := by
  have hp : ((38 : ℝ)/25)^3 < (2 : ℝ)^2 := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2)
    (by positivity : (0 : ℝ)<((38 : ℝ)/25)^3) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] at hl
  linarith

private theorem cyclic_normal_total (N M : Subgroup CyclicThree)
    (_hN : N.Normal) (_hM : M.Normal) : N≤M ∨ M≤N := by
  letI : Fact (Nat.card CyclicThree).Prime := ⟨by
    norm_num [CyclicThree,Nat.card_eq_fintype_card]⟩
  rcases N.eq_bot_or_eq_top_of_prime_card with rfl|rfl
  · exact Or.inl bot_le
  · exact Or.inr le_top

/-- Only the explicit existing Zmud literature input is used. -/
def cyclicCertificate (hZmud : ZmudFaithfulCharacterTupleInput)
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* CyclicThree) :
    PreE7Y1QuotientCertificate Q := by
  have hc : ∀ N M : Subgroup Q, N.Normal → M.Normal → N≤M ∨ M≤N :=
    normalSubgroups_total_of_surjective e.symm.toMonoidHom e.symm.surjective cyclic_normal_total
  have hg := socleNormalGeneratorBound_one_of_normal_total hc
  have hp : IsPGroup 3 Q :=
    (ZModModule.isPGroup_multiplicative (n:=3) (G:=ZMod 3)).of_equiv e.symm
  let C : CharacterQuotientCertificate Q :=
    { mode := .knownPGroup
      tuple := hZmud.generalTuple hg
      prime := 3
      known := fun _ => ⟨by norm_num,hp⟩ }
  exact .character C (by
    simpa only [CharacterQuotientCertificate.slope,C,
      ZmudFaithfulCharacterTupleInput.generalTuple_binaryCount,
      ZmudFaithfulCharacterTupleInput.generalTuple_linearCount,
      ZmudFaithfulCharacterTupleInput.generalTuple_generalCount,
      CharacterQuotientMode.generalSlope,Nat.cast_zero,Nat.cast_one,
      zero_mul,zero_add,one_mul] using known_slope)

variable {Q : Type} [Group Q] [Finite Q]
  (top : Q →* CyclicThree) (htop : Function.Surjective top)
  (A : Rep (ZMod 2) CyclicThree) (E : OriginalKernelModuleChart top A)
  (D : CubicBinaryCoordinates A.ρ)
  (hzero : ∀ (j : Fin 2) (v : A), D.invariant j v=0)

/-- Every original denominator is handled by the same coordinate dichotomy. -/
def certificate (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7Y1QuotientCertificate Q := by
  let s := scalar top A.ρ E.equiv.symm D
  let a := invariant top A.ρ E.equiv.symm D
  have ha : ∀ (j : Fin 2) (p : top.ker), a j p=1 := by
    intro j p
    change Multiplicative.ofAdd (D.invariant j (Multiplicative.toAdd (E.equiv.symm p)))=1
    rw [hzero]
    rfl
  have hconj := CubicKernelCoordinateEnvelope.inverseChart_conjugate top A E
  by_cases hs : ∃ j : Fin 2, ∃ p : top.ker, s j p ≠ 1
  · let j := Classical.choose hs
    let hp := Classical.choose_spec hs
    let C := CubicKernelNonzeroHead.jointData top htop A.ρ E.equiv.symm D hconj j hp
    have hcenter : C.headed.center=⊥ := by
      apply le_antisymm _ bot_le
      intro z hz
      apply Subgroup.mem_bot.mpr
      apply C.joint
      apply Prod.ext
      · apply Prod.ext
        · exact (ha 0 z).trans (map_one (C.invariant 0)).symm
        · exact (ha 1 z).trans (map_one (C.invariant 1)).symm
      · apply Prod.ext
        · exact (C.headed.coord_center C.first z hz).trans (map_one (C.headed.coord C.first)).symm
        · exact (C.headed.coord_center C.second z hz).trans (map_one (C.headed.coord C.second)).symm
    exact .headed C.headed (by
      change 2+Nat.log 2 (Nat.card C.headed.center) ≤ 3
      rw [hcenter]
      norm_num)
  · have hz : ∀ j p, s j p=1 := by
      intro j p
      by_contra hn
      exact hs ⟨j,p,hn⟩
    have hkernel : ∀ p : top.ker, p=1 := by
      intro p
      apply CubicElementaryKernelCoordinates.joint top A.ρ E.equiv.symm D
      apply Prod.ext
      · exact Prod.ext ((ha 0 p).trans (map_one (a 0)).symm)
          ((ha 1 p).trans (map_one (a 1)).symm)
      · exact Prod.ext ((hz 0 p).trans (map_one (s 0)).symm)
          ((hz 1 p).trans (map_one (s 1)).symm)
    have hinj : Function.Injective top := by
      intro x y hxy
      have hk : x*y⁻¹∈top.ker := by
        apply MonoidHom.mem_ker.mpr
        rw [map_mul,map_inv,hxy,mul_inv_cancel]
      have he := congrArg Subtype.val (hkernel ⟨x*y⁻¹,hk⟩)
      exact mul_inv_eq_one.mp he
    exact cyclicCertificate hZmud (MulEquiv.ofBijective top ⟨hinj,htop⟩)

end SymmetricSubgroupAsymptotics.PureCubicKernelY1Certificate
end
