import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongRootFamilyCover
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedDerivedMatrixLift
import SymmetricSubgroupAsymptotics.CFSGSimpleConjugateFamilyIndex

/-! The full ambient highest-root family under genuinely fixed D4
matrices has weighted size M*q^3 <= 6*q^12. It therefore has square less
than q^24, including q=2. Original projective transport is separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootFamilyCardinality
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityGeckSectionHeightMembership
open CFSGTrialityGeckFixedDerivedMatrixLift CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckLongRootFamilyCover CFSGTrialityGeckLongRootOrbitCardinality
open CFSGSerreOrdinaryTwists

local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) :=
  Classical.decEq _

def fixedRootFamily (q : CFSG.PrimePower) :=
  Set.range (fun g : FixedMatrixGroup q =>
    (RootLine (q.Extension 3) (longRoot 2)).map (MulAut.conj g.val.val).toMonoidHom)

theorem fixed_root_family_card_le_sum (q : CFSG.PrimePower) :
    Nat.card (fixedRootFamily q) ≤
      ∑ k : Bool × Fin 3, Nat.card (longRootOrbit q k.1 k.2) := by
  have hcover (x : fixedRootFamily q) :
      ∃ k : Bool × Fin 3, ∃ y : longRootOrbit q k.1 k.2, y.val = x.val := by
    obtain ⟨g,hg⟩ := x.property
    have ht : matrixGroupTwist (q.Extension 3) (definingFieldAutomorphism q 3) g.val = g.val :=
      g.property
    have hf := (matrixGroupTwist_val (q.Extension 3) (definingFieldAutomorphism q 3) g.val).symm.trans
      (congrArg (fun z : CFSGTrialityGeckSourceWordAction.MatrixGroup (q.Extension 3) => z.val) ht)
    obtain ⟨neg,s,u,hu⟩ := conjugate_eq_fixed_positive_conjugate q g.val.val g.val.property hf
    exact ⟨(neg,s),⟨_,⟨u,rfl⟩⟩,hu.symm.trans hg⟩
  let idx (x : fixedRootFamily q) : Bool × Fin 3 := Classical.choose (hcover x)
  let term (x : fixedRootFamily q) : longRootOrbit q (idx x).1 (idx x).2 :=
    Classical.choose (Classical.choose_spec (hcover x))
  have hterm (x : fixedRootFamily q) : (term x).val = x.val :=
    Classical.choose_spec (Classical.choose_spec (hcover x))
  let enc : fixedRootFamily q →
      (k : Bool × Fin 3) × longRootOrbit q k.1 k.2 := fun x => ⟨idx x,term x⟩
  have hinj : Function.Injective enc := by
    intro x y he
    apply Subtype.ext
    have hh := congrArg (fun z : (k : Bool × Fin 3) × longRootOrbit q k.1 k.2 => z.2.val) he
    change (term x).val = (term y).val at hh
    rwa [hterm,hterm] at hh
  calc
    _ ≤ Nat.card ((k : Bool × Fin 3) × longRootOrbit q k.1 k.2) :=
      Nat.card_le_card_of_injective enc hinj
    _ = _ := Nat.card_sigma

theorem fixed_root_family_card_mul_cube_le (q : CFSG.PrimePower) :
    Nat.card (fixedRootFamily q) * q.order ^ 3 ≤ 6 * q.order ^ 12 := by
  calc
    _ ≤ (∑ k : Bool × Fin 3, Nat.card (longRootOrbit q k.1 k.2)) * q.order ^ 3 :=
      Nat.mul_le_mul_right _ (fixed_root_family_card_le_sum q)
    _ = ∑ k : Bool × Fin 3, Nat.card (longRootOrbit q k.1 k.2) * q.order ^ 3 :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ _k : Bool × Fin 3, q.order ^ 12 := by
      apply Finset.sum_le_sum
      intro k _
      exact long_root_orbit_card_mul_cube_le q k.1 k.2
    _ = _ := by
      have hi : Fintype.card (Bool × Fin 3) = 6 := by decide
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hi]

theorem fixed_root_family_square_lt (q : CFSG.PrimePower) :
    Nat.card (fixedRootFamily q) ^ 2 < q.order ^ 24 := by
  have hq : 2 ≤ q.order := by
    calc
      2 ≤ q.prime := q.prime_isPrime.two_le
      _ = q.prime ^ 1 := (pow_one _).symm
      _ ≤ q.prime ^ q.exponent := Nat.pow_le_pow_right q.prime_isPrime.pos q.exponent_pos
  have hcube : 6 < q.order ^ 3 := by
    have h := Nat.pow_le_pow_left hq 3
    norm_num at h
    omega
  exact CFSGSimpleConjugateFamilyIndex.square_lt_of_weighted_family q.order 12 3 6
    (Nat.card (fixedRootFamily q)) (q.order ^ 24) (by omega) hcube
      (fixed_root_family_card_mul_cube_le q) (by norm_num)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootFamilyCardinality
