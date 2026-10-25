import SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalOrderBound
import SymmetricSubgroupAsymptotics.FiniteHermitianSpecialDeterminantSaving
import SymmetricSubgroupAsymptotics.CFSGUnitaryHermitianScalarCardinality
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoNormOneWeight

/-! Sharp frame and determinant counts retain the ORIGINAL isometry
group even when its signed form first needs a nonzero scalar multiple
to become Hermitian. Scalar cancellation supplies the actual witnesses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteHermitianScaledSpecialOrderBound
open Module CFSGTwistedAUnitaryParameters CFSGHermitianSimilitudeGroup
open CFSGSerreOrdinaryTwists FiniteHermitianOrthonormalCoordinates
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem isometries_card_le (q : CFSG.PrimePower)
    (H : (Matrix I I (q.Extension 2))ˣ) (c : q.Extension 2)
    {n : ℕ} (b : Basis (Fin n) (q.Extension 2) (I → q.Extension 2))
    (hb : ∀ i j, hermitianPair (definingFieldAutomorphism q 2) (c • H.val)
      (b i) (b j)=if i=j then 1 else 0) :
    Nat.card (isometries (definingFieldAutomorphism q 2) H) ≤ 3*q.order^(n^2) := by
  let sigma := definingFieldAutomorphism q 2
  letI : Finite (LinearGroup (K := q.Extension 2) (I := I)) :=
    Finite.of_injective (fun e : LinearGroup (K := q.Extension 2) (I := I) =>
      (e : (I → q.Extension 2) → I → q.Extension 2)) DFunLike.coe_injective
  apply FiniteHermitianOrthonormalOrderBound.card_le_three_mul_square_power q b
    (isometries sigma H).subtype (isometries sigma H).subtype_injective
  intro g x y
  rw [←pairing_eq_coordinatePair sigma (c • H.val) b hb,
    ←pairing_eq_coordinatePair sigma (c • H.val) b hb]
  rw [CFSGHermitianMatrixPullback.scalar_form,
    CFSGHermitianMatrixPullback.scalar_form]
  change c*hermitianPair sigma H.val (g.val x) (g.val y)=
    c*hermitianPair sigma H.val x y
  exact congrArg (fun a : q.Extension 2 => c*a) (g.property x y)

private theorem determinant_surjective (q : CFSG.PrimePower)
    (H : (Matrix I I (q.Extension 2))ˣ) (c : q.Extension 2) (hc : c ≠ 0)
    {n : ℕ} (b : Basis (Fin n) (q.Extension 2) (I → q.Extension 2))
    (hb : ∀ i j, hermitianPair (definingFieldAutomorphism q 2) (c • H.val)
      (b i) (b j)=if i=j then 1 else 0) (i₀ : Fin n) :
    Function.Surjective (normOneDeterminantHom (definingFieldAutomorphism q 2) H) := by
  let sigma := definingFieldAutomorphism q 2
  intro z
  have hz : sigma (z.val : q.Extension 2)*(z.val : q.Extension 2)=1 :=
    congrArg (fun a : (q.Extension 2)ˣ => (a : q.Extension 2)) z.property
  obtain ⟨e,hp,hd⟩ := FiniteHermitianNormOneBasisScaling.exists_isometry_determinant
    sigma (c • H.val) b hb i₀ z.val hz
  have hporig (x y : I → q.Extension 2) :
      hermitianPair sigma H.val (e x) (e y)=hermitianPair sigma H.val x y := by
    apply mul_left_cancel₀ hc
    simpa only [CFSGHermitianMatrixPullback.scalar_form] using hp x y
  let u : isometries sigma H := ⟨e,hporig⟩
  refine ⟨u,?_⟩
  apply Subtype.ext
  apply Units.ext
  change (isometryDeterminantHom sigma H u : q.Extension 2)=(z.val : q.Extension 2)
  rw [FiniteHermitianSpecialDeterminantSaving.determinant_eq_linear]
  exact hd

theorem special_card_mul_normOne_le (q : CFSG.PrimePower)
    (H : (Matrix I I (q.Extension 2))ˣ) (c : q.Extension 2) (hc : c ≠ 0)
    {n : ℕ} (b : Basis (Fin n) (q.Extension 2) (I → q.Extension 2))
    (hb : ∀ i j, hermitianPair (definingFieldAutomorphism q 2) (c • H.val)
      (b i) (b j)=if i=j then 1 else 0) (i₀ : Fin n) :
    (q.order+1)*Nat.card (specialIsometries (definingFieldAutomorphism q 2) H) ≤
      3*q.order^(n^2) := by
  let sigma := definingFieldAutomorphism q 2
  let f := normOneDeterminantHom sigma H
  have hk : f.ker=specialIsometries sigma H := MonoidHom.ker_codRestrict _ _ _
  have hr : f.range=⊤ := MonoidHom.range_eq_top.mpr
    (determinant_surjective q H c hc b hb i₀)
  have hcard : Nat.card (isometries sigma H)=
      Nat.card (specialIsometries sigma H)*Nat.card (normOneUnits sigma) := by
    calc
      _ = Nat.card f.ker*Nat.card f.range := by
        rw [←f.ker.card_mul_index,Subgroup.index_ker]
      _ = _ := by
        rw [hk,hr,Nat.card_congr (Subgroup.topEquiv :
          (⊤ : Subgroup (normOneUnits sigma)) ≃* normOneUnits sigma).toEquiv]
  have hn : Nat.card (normOneUnits sigma)=q.order+1 := by
    rw [CFSGUnitaryHermitianScalarCardinality.normOneUnits_eq,
      CFSGTwistedAUnitaryCoordinates.quadratic_normOneUnits_card]
  have hh := isometries_card_le q H c b hb
  rw [hcard,hn] at hh
  simpa only [Nat.mul_comm] using hh

end SymmetricSubgroupAsymptotics.FiniteHermitianScaledSpecialOrderBound
