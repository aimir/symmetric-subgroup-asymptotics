import SymmetricSubgroupAsymptotics.CFSGOddNilpotentCoarseNormalRank

/-! Actual mixed odd sectors have an improved rank budget. Their two
nontrivial coprime factor degrees are at least three and multiply to the
original physical degree; no replacement degree or factor menu is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOddNilpotentMixedNormalRank
open MarkedC4 CFSGOddNilpotentCoarseNormalRank

/-- The n/9 mixed-sector saving keeps every original normal subgroup. -/
theorem normalGen_real_le_ninth
    {P O X : Type} [Group P] [Group O] [Finite P] [Finite O]
    [Group.IsNilpotent P] [Group.IsNilpotent O] [Nontrivial P] [Nontrivial O]
    [Finite X] [Nonempty X] [MulAction (P × O) X] [FaithfulSMul (P × O) X]
    [MulAction.IsPretransitive (P × O) X]
    (hcop : Nat.Coprime (Nat.card P) (Nat.card O))
    (hPodd : ¬2 ∣ Nat.card P) (hOodd : ¬2 ∣ Nat.card O)
    (N : Subgroup (P × O)) [N.Normal] :
    (normalGen N : ℝ) ≤ (Nat.card X : ℝ)/9 := by
  let x : X := Classical.arbitrary X
  let A := CFSGCoprimeTransitiveFactorActions.LeftFiber (P := P) (O := O) x
  let B := CFSGCoprimeTransitiveFactorActions.RightFiber (P := P) (O := O) x
  letI : FaithfulSMul P A := CFSGCoprimeTransitiveFactorActions.left_faithful hcop x
  letI : FaithfulSMul O B := CFSGCoprimeTransitiveFactorActions.right_faithful hcop x
  have hA3 : 3 ≤ Nat.card A := coset_degree_ge_three _ hPodd
  have hB3 : 3 ≤ Nat.card B := coset_degree_ge_three _ hOodd
  have hprod : Nat.card A*Nat.card B=Nat.card X :=
    CFSGCoprimeTransitiveFactorActions.degree_product hcop x
  let f : P × O →* P := MonoidHom.fst P O
  let g : P × O →* O := MonoidHom.snd P O
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f (fun a => ⟨(a,1),rfl⟩)
  letI : (N.map g).Normal := Subgroup.Normal.map inferInstance g (fun b => ⟨(1,b),rfl⟩)
  have hleft := normalGen_real_le_third (X := A) hPodd (N.map f)
  have hright := normalGen_real_le_third (X := B) hOodd (N.map g)
  have hm := CFSGCoprimeProductNormalGenerators.normalGen_le_max hcop N
  have hmR : (normalGen N : ℝ) ≤ max (normalGen (N.map f) : ℝ) (normalGen (N.map g) : ℝ) := by
    exact_mod_cast hm
  have hpr : (Nat.card A : ℝ)*(Nat.card B : ℝ)=Nat.card X := by exact_mod_cast hprod
  have haR : (3 : ℝ) ≤ Nat.card A := by exact_mod_cast hA3
  have hbR : (3 : ℝ) ≤ Nat.card B := by exact_mod_cast hB3
  apply hmR.trans (max_le _ _)
  · apply hleft.trans
    nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.card A)) (sub_nonneg.mpr hbR)]
  · apply hright.trans
    nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.card B)) (sub_nonneg.mpr haR)]

end SymmetricSubgroupAsymptotics.CFSGOddNilpotentMixedNormalRank
