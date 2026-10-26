import SymmetricSubgroupAsymptotics.CFSGReeFFourWholeOuterMiddleRelation
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareCommutator

/-! A whole-word reflection centralizing the actual outer involution.
The calculation uses the checked y/r conjugation on the WHOLE outer
word, not just its first matrix layer. All parameters remain abstract. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterCentralizingReflection
open CFSGReeFFourWholeOuterMiddleRelation CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourMiddleSquareCommutator CFSGReeFFourOuterThreeWord
open CFSGReeFFourFixedModelEquivalence

private theorem square_conjugate {G : Type*} [Group G] (y r x : G)
    (hxy : y*x*y⁻¹=r*x*r⁻¹) (hry : y*r*y⁻¹=r^2) :
    y^2*x*(y^2)⁻¹=r^3*x*(r^3)⁻¹ := by
  calc
    _=y*(y*x*y⁻¹)*y⁻¹ := by
      simp only [pow_succ,pow_zero,one_mul]
      group
    _=y*(r*x*r⁻¹)*y⁻¹ := by rw [hxy]
    _=(y*r*y⁻¹)*(y*x*y⁻¹)*(y*r*y⁻¹)⁻¹ := by group
    _=r^2*(r*x*r⁻¹)*(r^2)⁻¹ := by rw [hry,hxy]
    _=_ := by group

private theorem square_inverts {G : Type*} [Group G] (y r : G)
    (hry : y*r*y⁻¹=r^2) (hr : r^5=1) : y^2*r*(y^2)⁻¹=r⁻¹ := by
  calc
    _=y*(y*r*y⁻¹)*y⁻¹ := by
      simp only [pow_succ,pow_zero,one_mul]
      group
    _=y*r^2*y⁻¹ := by rw [hry]
    _=(y*r*y⁻¹)^2 := by rw [pow_two,pow_two]; group
    _=r^4 := by rw [hry]; group
    _=r^5*r⁻¹ := by group
    _=r⁻¹ := by rw [hr,one_mul]

private theorem reflection_value {G : Type*} [Group G] (r t : G)
    (ht : t*r*t⁻¹=r⁻¹) (hr : r^5=1) :
    r*t*r⁻¹=(r^3)⁻¹*t := by
  have hi : t*r⁻¹*t⁻¹=r := by
    calc
      _=(t*r*t⁻¹)⁻¹ := by group
      _=(r⁻¹)⁻¹ := congrArg Inv.inv ht
      _=r := inv_inv r
  calc
    _=r*(t*r⁻¹*t⁻¹)*t := by group
    _=r*r*t := by rw [hi]
    _=r^2*t := by rw [pow_two]
    _=(r^3)⁻¹*(r^3*r^2)*t := by rw [inv_mul_cancel_left]
    _=(r^3)⁻¹*r^5*t := by rw [←pow_add]
    _=_ := by rw [hr,mul_one]

private theorem centralizes {G : Type*} [Group G] (r t x : G)
    (hval : r*t*r⁻¹=(r^3)⁻¹*t)
    (hx : t*x*t⁻¹=r^3*x*(r^3)⁻¹) : Commute (r*t*r⁻¹) x := by
  have hc : (r*t*r⁻¹)*x*(r*t*r⁻¹)⁻¹=x := by
    calc
      _=(r^3)⁻¹*(t*x*t⁻¹)*r^3 := by rw [hval]; group
      _=(r^3)⁻¹*(r^3*x*(r^3)⁻¹)*r^3 := by rw [hx]
      _=x := by group
  exact mul_inv_eq_iff_eq_mul.mp hc

def reflectionWord (m : ℕ) : originalModelFixed m :=
  fiveWord m*(fourCycle m)^2*(fiveWord m)⁻¹

theorem square_outer_conjugation (m : ℕ) :
    (fourCycle m)^2*outerInvolution m*((fourCycle m)^2)⁻¹=
      (fiveWord m)^3*outerInvolution m*((fiveWord m)^3)⁻¹ :=
  square_conjugate _ _ _ (outer_middle_conjugation m) (fiveWord_conjugate m)

theorem square_five_conjugation (m : ℕ) :
    (fourCycle m)^2*fiveWord m*((fourCycle m)^2)⁻¹=(fiveWord m)⁻¹ :=
  square_inverts _ _ (fiveWord_conjugate m) (fiveWord_pow_five m)

theorem reflectionWord_value (m : ℕ) :
    reflectionWord m=((fiveWord m)^3)⁻¹*(fourCycle m)^2 :=
  reflection_value _ _ (square_five_conjugation m) (fiveWord_pow_five m)

theorem reflectionWord_square (m : ℕ) : (reflectionWord m)^2=1 := by
  change (fiveWord m*(fourCycle m)^2*(fiveWord m)⁻¹)^2=1
  calc
    _=fiveWord m*(fourCycle m)^4*(fiveWord m)⁻¹ := by
      simp only [pow_succ,pow_zero,one_mul]
      group
    _=1 := by rw [fourCycle_four]; group

theorem reflectionWord_mem_derived (m : ℕ) :
    reflectionWord m∈commutator (originalModelFixed m) :=
  (commutator (originalModelFixed m)).mul_mem
    ((commutator (originalModelFixed m)).mul_mem (fiveWord_mem_commutator m)
      (square_mem_derived m))
    ((commutator (originalModelFixed m)).inv_mem (fiveWord_mem_commutator m))

theorem reflectionWord_commutes_outer (m : ℕ) :
    Commute (reflectionWord m) (outerInvolution m) :=
  centralizes _ _ _ (reflectionWord_value m) (square_outer_conjugation m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterCentralizingReflection
