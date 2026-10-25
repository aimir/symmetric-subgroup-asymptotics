import SymmetricSubgroupAsymptotics.EightPointHalfDegreeFiniteModelReduction
import SymmetricSubgroupAsymptotics.GeneralFourTwoAlternatingEquiv
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenOrdinaryGenerators

/-! The actual binary GL4 complement action on eight points pays original
affine16 rank at most five OR returns an exact failed primitive sporadic
action on at most eight points. The failure witness is global and is NOT
asserted to be a subquotient of the affine group. This is a finite-model
reduction, not an unconditional affine16 sharp theorem. No new generator
hypothesis, finite catalogue, or current-degree Tracey/MN input occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenEightPointSharpReduction
open EightPointHalfDegreeFiniteModelReduction TraceySharpHalfDegreeNumerics

theorem genRank_le_four_of_injective_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) {H : Type} [Group H] [Finite H]
    (f : H →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) (hf : Function.Injective f) :
    MarkedC4.genRank H ≤ 4 ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  let rho : H →* Equiv.Perm (Fin 8) := GeneralFourTwoAlternatingEquiv.eightAction.comp f
  have hrho : Function.Injective rho := GeneralFourTwoAlternatingEquiv.eightAction_injective.comp hf
  let e : H ≃* rho.range := MonoidHom.ofInjective hrho
  rcases EightPointHalfDegreeFiniteModelReduction.genRank_le_four_or_sporadic_counterexample
    hCFSG rho.range with hp | hbad
  · exact Or.inl ((CoprimeNilpotentProductGenerators.genRank_mulEquiv e).le.trans hp)
  · exact Or.inr hbad

private theorem complement_bound (hCFSG : CFSG.CFSGClassification)
    {H : Type} [Group H] [Finite H] (p d : ℕ) [Fact p.Prime]
    (hp : p = 2) (hd : d = 4)
    (f : H →* Matrix.GeneralLinearGroup (Fin d) (ZMod p)) (hf : Function.Injective f) :
    MarkedC4.genRank H ≤ 4 ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  subst p
  subst d
  exact genRank_le_four_of_injective_or_sporadic_counterexample hCFSG f hf

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem genRank_le_five_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hprimitive : MulAction.IsPreprimitive G X)
    (hdegree : Nat.card X = 16) :
    MarkedC4.genRank G ≤ 5 ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  let C := P.elementaryChart hprimitive
  let x : X := Classical.arbitrary X
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hpow : P.p^C.d = 16 := by
    have he := P.degree_eq_prime_pow_finrank C.equiv x
    simpa only [PrimitiveAffineProfile.ElementaryChart.d,hdegree] using he.symm
  have hpdiv : P.p ∣ 2^4 := by
    change P.p ∣ 16
    rw [← hpow]
    exact dvd_pow_self _ C.d_pos.ne'
  have hp : P.p = 2 := Nat.prime_eq_prime_of_dvd_pow P.p_prime (by decide) hpdiv
  have hd : C.d = 4 := Nat.pow_right_injective (by decide : 2 ≤ 2)
    (by simpa only [hp] using hpow)
  let f0 : P.complement x →* Matrix.GeneralLinearGroup (Fin C.d) (ZMod P.p) :=
    FaithfulFiniteLinearRepresentationOrder.matrixHom
      (P.complementRepresentationCore hprimitive C x).ρ
  have hf0 : Function.Injective f0 :=
    FaithfulFiniteLinearRepresentationOrder.matrixHom_injective _
      (P.complementRepresentationCore_injective hprimitive C x)
  rcases complement_bound hCFSG P.p C.d hp hd f0 hf0 with hhead | hbad
  · exact Or.inl ((P.genRank_le_complement_add_one hprimitive x).trans (by omega))
  · exact Or.inr hbad

include P in
theorem genRank_le_sharpFloor_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hprimitive : MulAction.IsPreprimitive G X)
    (hdegree : Nat.card X = 16) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) ∨ Nonempty (PrimitiveSporadicCounterexample 8) := by
  rcases genRank_le_five_or_sporadic_counterexample P hCFSG hprimitive hdegree with hp | hbad
  · have hnum := PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.five_le_sharpFloor_of_band
      16 (by decide) (by decide)
    exact Or.inl (hp.trans (by simpa only [hdegree] using hnum))
  · exact Or.inr hbad

include P in
theorem exists_generating_finset_or_sporadic_counterexample
    (hCFSG : CFSG.CFSGClassification) (hprimitive : MulAction.IsPreprimitive G X)
    (hdegree : Nat.card X = 16) :
    (∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ 5) ∨
      Nonempty (PrimitiveSporadicCounterexample 8) := by
  rcases genRank_le_five_or_sporadic_counterexample P hCFSG hprimitive hdegree with hp | hbad
  · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := G)
    exact Or.inl ⟨S,hgen,hcard.le.trans hp⟩
  · exact Or.inr hbad

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenEightPointSharpReduction
