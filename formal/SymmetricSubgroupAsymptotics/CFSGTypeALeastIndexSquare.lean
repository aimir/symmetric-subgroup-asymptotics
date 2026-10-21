import SymmetricSubgroupAsymptotics.CFSGTypeAGeneralLinearProductLower
import SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! The exact square/index inequality for every original higher-rank
PSL, obtained by cardinal cancellation from GL and the actual point
stabilizer. No subgroup classification or SL order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeALeastIndexSquare
open PrimitiveSocleRawStructure CFSGTypeAProjectivePointIndex
open CFSGTypeAGeneralLinearCardBound CFSGTypeAGeneralLinearProductLower
variable {F : Type} [Field F] [Finite F]

private theorem mul_square_swap (a b : ℕ) : a^2*b^2=(b*a)^2 := by ring

theorem leastProperIndex_square_lt_card (n : ℕ) (hn : 3≤n) (ell : ℕ)
    (hell : LeastProperIndex (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) ell) :
    ell^2<Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) := by
  obtain ⟨H,hH,hi⟩ := exists_proper_subgroup_of_point_index (F:=F) n (by omega)
  have he : ell≤Nat.card (Points F n) := (hell.2 H hH).trans_eq hi
  have hpoints := points_card_mul_units (F:=F) n
  have hscale : (Nat.card F-1)^2*ell^2≤(Nat.card F^n-1)^2 := by
    calc
      (Nat.card F-1)^2*ell^2≤(Nat.card F-1)^2*Nat.card (Points F n)^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he 2)
      _=(Nat.card (Points F n)*(Nat.card F-1))^2 := mul_square_swap _ _
      _=(Nat.card F^n-1)^2 := congrArg (fun k : ℕ => k^2) hpoints
  have hgl := generalLinear_card_gt_power_sub_one_square F n hn
  have hfactor := generalLinear_card_le_units_sq_mul_projective (F:=F) (n:=Fin n)
  rw [Nat.card_units] at hfactor
  have hstrict : (Nat.card F-1)^2*ell^2<
      (Nat.card F-1)^2*Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) :=
    hscale.trans_lt (hgl.trans_le hfactor)
  by_contra hh
  have hle : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin n) F)≤ell^2 := by omega
  have hm := Nat.mul_le_mul_left ((Nat.card F-1)^2) hle
  omega

theorem typeA_leastProperIndex_square_lt_card (r : ℕ) (hr : 2≤r)
    (q : CFSG.PrimePower) (ell : ℕ) (hell : LeastProperIndex (CFSG.Models.A r q) ell) :
    ell^2<Nat.card (CFSG.Models.A r q) :=
  leastProperIndex_square_lt_card (F:=q.Field) (r+1) (by omega) ell hell

end SymmetricSubgroupAsymptotics.CFSGTypeALeastIndexSquare
