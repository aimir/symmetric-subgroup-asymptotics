import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedTorusAction
import Mathlib.Data.Finset.Card

/-! Any torus unit different from 1 and -1 acts without nonidentity
fixed points on the actual positive Ree subgroup. Such a unit exists
for every simple-family parameter m at least one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedTorusRegularity
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalTorus
open CFSGReeGTwoFixedTorusAction CFSGGTwoNaturalPositiveTorusAction
open CFSGReeGTwoOriginalFixedWordChart CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoFixedCoordinateArithmetic CFSGGTwoPositiveWordSubgroup

private theorem alpha_square (m : ℕ) (x : Field m) (hx : x≠0)
    (h : alpha m x=x^2) : x=1 := by
  have hh := congrArg (alpha m) h
  rw [alpha_twice, map_pow, h] at hh
  have hp : x^3*1=x^3*x := by
    calc
      x^3*1 = (x^2)^2 := by simpa only [mul_one] using hh
      _ = x^3*x := by ring
  exact (mul_left_cancel₀ (pow_ne_zero 3 hx) hp).symm

private theorem alpha_fixed (m : ℕ) (x : Field m) (hx : x≠0)
    (h : alpha m x=x) : x=1 ∨ x=-1 := by
  have hh := congrArg (alpha m) h
  rw [alpha_twice, h] at hh
  have hp : x*x^2=x*1 := by simpa only [←pow_succ',mul_one] using hh
  exact (sq_eq_one_iff).mp (mul_left_cancel₀ hx hp)

theorem rootScale_zero_ne_one (m : ℕ) (t : (Field m)ˣ) (ht : t≠1) :
    (rootScale (Field m) (t,unitsAlpha m t) 0 : Field m)≠1 := by
  intro h
  have hu : t^2*(unitsAlpha m t)⁻¹=1 := Units.ext h
  have hp : alpha m (t : Field m)=(t : Field m)^2 := by
    have hv := congrArg (fun z : (Field m)ˣ => (z : Field m))
      (mul_inv_eq_one.mp hu).symm
    exact hv
  exact ht (Units.ext (alpha_square m (t : Field m) (Units.ne_zero t) hp))

theorem rootScale_two_ne_one (m : ℕ) (t : (Field m)ˣ)
    (ht : t≠1) (htn : t≠-1) :
    (rootScale (Field m) (t,unitsAlpha m t) 2 : Field m)≠1 := by
  intro h
  have hu : t⁻¹*unitsAlpha m t=1 := Units.ext h
  have hp : alpha m (t : Field m)=(t : Field m) :=
    congrArg (fun z : (Field m)ˣ => (z : Field m)) (inv_mul_eq_one.mp hu).symm
  rcases alpha_fixed m (t : Field m) (Units.ne_zero t) hp with h1 | hn
  · exact ht (Units.ext h1)
  · exact htn (Units.ext hn)

theorem rootScale_three_ne_one (m : ℕ) (t : (Field m)ˣ) (ht : t≠1) :
    (rootScale (Field m) (t,unitsAlpha m t) 3 : Field m)≠1 := by
  intro h
  exact ht (Units.ext h)

private theorem scalar_fixed_zero {K : Type*} [Field K] (s y : K)
    (hs : s≠1) (hy : y*s=y) : y=0 := by
  have he : y*(s-1)=0 := by rw [mul_sub,mul_one,hy,sub_self]
  exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hs)

theorem fixedScaleCoordinates_eq_self (m : ℕ) (t : (Field m)ˣ)
    (ht : t≠1) (htn : t≠-1) (y : Fin 3 → Field m)
    (hy : fixedScaleCoordinates m t y=y) : y=0 := by
  have h0 := congrFun hy 0
  have h1 := congrFun hy 1
  have h2 := congrFun hy 2
  funext i
  fin_cases i
  · exact scalar_fixed_zero _ _ (rootScale_zero_ne_one m t ht) h0
  · exact scalar_fixed_zero _ _ (rootScale_two_ne_one m t ht htn) h1
  · exact scalar_fixed_zero _ _ (rootScale_three_ne_one m t ht) h2

private theorem fixedWord_zero (m : ℕ) : fixedWord m 0=1 := by
  apply Subtype.ext
  change CFSGGTwoPositiveSixWord.modelWord (Field m)
    (normalForm (alphaEquiv m) 0 0 0)=1
  have hn : normalForm (alphaEquiv m) 0 0 0=0 := by
    funext i
    fin_cases i <;> simp [normalForm]
  rw [hn,modelWord_zero]

theorem fixedTorus_centralizer_positive (m : ℕ) (t : (Field m)ˣ)
    (ht : t≠1) (htn : t≠-1) (u : fixedPositiveGroup m)
    (hu : fixedTorusHom m t*u.val*(fixedTorusHom m t)⁻¹=u.val) : u=1 := by
  obtain ⟨y,hy⟩ := fixedPositiveChart_surjective m u
  have he : fixedWord m (fixedScaleCoordinates m t y)=fixedWord m y := by
    rw [←fixedTorus_fixedWord]
    change fixedTorusHom m t*(fixedPositiveChart m y).val*
      (fixedTorusHom m t)⁻¹=(fixedPositiveChart m y).val
    rw [hy]
    exact hu
  have hz := fixedScaleCoordinates_eq_self m t ht htn y (fixedWord_injective m he)
  apply Subtype.ext
  change u.val=1
  rw [←hy]
  change fixedWord m y=1
  rw [hz,fixedWord_zero]

theorem exists_regular_unit (m : ℕ) (hm : 1≤m) :
    ∃ t : (Field m)ˣ, t≠1 ∧ t≠-1 := by
  classical
  letI : Fintype ((Field m)ˣ) := Fintype.ofFinite _
  have hq : 27≤3^(2*m+1) := by
    exact Nat.pow_le_pow_right (by decide : 1≤3) (by omega : 3≤2*m+1)
  have hc : 2<Fintype.card ((Field m)ˣ) := by
    have hn : 2<Nat.card ((Field m)ˣ) := by
      rw [Nat.card_units,field_card]
      omega
    simpa only [Nat.card_eq_fintype_card] using hn
  have hs : ({1,-1} : Finset ((Field m)ˣ)).card≤2 := Finset.card_insert_le _ _ |>.trans (by simp)
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1,-1} : Finset ((Field m)ˣ))) (t := Finset.univ)
    (hs.trans_lt (by simpa only [Finset.card_univ] using hc))
  exact ⟨t,by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using ht⟩

end SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedTorusRegularity
