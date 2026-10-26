import SymmetricSubgroupAsymptotics.CFSGReeFFourPenultimateMiddleIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionDiagonalResidual
import SymmetricSubgroupAsymptotics.CFSGReeFFourSignedBlockGeneration

/-! Actual binary Weyl relations for the length-seven middle-block flag.
The diagonal residuals are killed only by the proved literal binary
fixed-diagonal triviality. All algebraic normalization is abstract group
algebra; no automorphism is lifted to the ambient group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPenultimateWeyl
open CFSGReeFFourPenultimateMiddleIntersection CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourOppositionDiagonalResidual CFSGReeFFourBinaryMiddleGenerators
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedBruhatCover
open CFSGReeFFourMinimalParabolics CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourSignedBlockGeneration
open CFSGReeFFourInversionPeelingWords CFSGReeFFourMiddleDerivedFiveWord

private theorem diagonal_eq_one (x : originalModelFixed 0) (hx : x∈fixedDiagonal 0) : x=1 :=
  Subgroup.mem_bot.mp ((le_of_eq fixedDiagonal_zero_eq_bot) hx)

private theorem square_of_product {G : Type*} [Group G] (x : G) (h : x*x=1) : x^2=1 :=
  (pow_two x).trans h

private theorem commute_of_residual {G : Type*} [Group G] (a b : G)
    (h : a*b*a⁻¹*b⁻¹=1) : Commute a b := by
  have he : a*b*a⁻¹=b := mul_inv_eq_one.mp h
  have hh := congrArg (fun x : G => x*a) he
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

private theorem reflection_word {G : Type*} [Group G] (a b : G) (hb : b^2=1) :
    (a*b)^3*a=(a*b)^4*b := by
  have hbb : b*b=1 := (pow_two b).symm.trans hb
  calc
    _=((a*b)^3*a)*(b*b) := by rw [hbb,mul_one]
    _=((a*b)^3*(a*b))*b := by group
    _=(a*b)^4*b := congrArg (fun x : G => x*b) (pow_succ (a*b) 3).symm

theorem short_thirteen_word (m : ℕ) :
    shortModelWord m (13 : Fin 16)=
      (outerFixedWeyl m*middleFixedWeyl m)^3*outerFixedWeyl m := by
  change fixedPairedWord m ([false]++([true]++([false]++([true]++
    ([false]++([true]++[false]))))))=_
  simp only [fixedPairedWord_append]
  change simpleWeyl m false*(simpleWeyl m true*(simpleWeyl m false*
    (simpleWeyl m true*(simpleWeyl m false*(simpleWeyl m true*simpleWeyl m false)))))=_
  rw [simpleWeyl_false,simpleWeyl_true]
  simp only [pow_succ,pow_zero,one_mul,mul_assoc]

theorem binary_opposition_square : (oppositionFixed 0)^2=1 :=
  square_of_product _ (diagonal_eq_one _ (opposition_square_mem_diagonal 0))

theorem binary_opposition_commute_simple (b : Bool) :
    Commute (oppositionFixed 0) (simpleWeyl 0 b) :=
  commute_of_residual _ _
    (diagonal_eq_one _ (opposition_simple_residual_mem_diagonal 0 b))

theorem binary_short_thirteen_eq :
    shortModelWord 0 (13 : Fin 16)=oppositionFixed 0*middleFixedWeyl 0 := by
  have ho := opposition_eq_simpleWeyl_power 0
  rw [simpleWeyl_false,simpleWeyl_true] at ho
  exact (short_thirteen_word 0).trans
    ((reflection_word _ _ (middleWeyl_square 0)).trans
      (congrArg (fun x : originalModelFixed 0 => x*middleFixedWeyl 0) ho.symm))

theorem binary_short_thirteen_square : (shortModelWord 0 (13 : Fin 16))^2=1 := by
  have hc : Commute (oppositionFixed 0) (middleFixedWeyl 0) := by
    simpa only [simpleWeyl_true] using binary_opposition_commute_simple true
  rw [binary_short_thirteen_eq,hc.mul_pow,binary_opposition_square,middleWeyl_square,one_mul]

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPenultimateWeyl
