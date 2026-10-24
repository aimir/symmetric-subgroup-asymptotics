import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveHeightTorus
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalCardinality

/-! The genuine fixed diagonal has no nonidentity fixed point in the
full positive subgroup for m>0. All ambient height coordinates have
nontrivial actual torus characters, so the checked height kernels force
an invariant element through the filtration to its trivial last tail. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDiagonalCentralizer
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourPositiveHeightCoordinates CFSGReeFFourPositiveHeightTorus
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedTorusGroup CFSGReeFFourFixedDiagonalCardinality
open CFSGNormTwoCoordinateExactHeightLayer CFSGNormTwoCoordinateRootHeightBound
local notation "A" => CartanMatrix.E₆
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem coordinate_eq_one_of_fixed_torus (m : ℕ) (hm : 0<m)
    (h : ℤ) (hh : 0<h) (u : tail m h)
    (hfixed : ∀ t : (Field m)ˣ×(Field m)ˣ,torusConjugate m h t u=u) :
    coordinateHom m h hh u=1 := by
  change (coordinateHom m h hh u).toAdd=0
  funext k
  obtain ⟨t,ht⟩ := CFSGReeFFourRootTorusCharacters.rootCharacter_nontrivial m hm k.val.val
  have htval : (CFSGReeFFourRootTorusCharacters.rootCharacter m k.val.val t : Field m)≠1 := by
    intro he
    exact ht (Units.ext he)
  have he := torusConjugate_coordinate m h hh t u k
  rw [hfixed t] at he
  have hz : ((CFSGReeFFourRootTorusCharacters.rootCharacter m k.val.val t : Field m)-1)*
      (coordinateHom m h hh u).toAdd k=0 := by
    rw [sub_mul,one_mul,←he,sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr htval)

theorem positive_eq_one_of_fixed_torus (m : ℕ) (hm : 0<m) (u : fixedPositive m)
    (hfixed : ∀ t : (Field m)ˣ×(Field m)ˣ,
      fixedTorusHom m t*u.val*(fixedTorusHom m t)⁻¹=u.val) : u=1 := by
  have htail : ∀ n : ℕ,u∈tail m ((n : ℤ)+1) := by
    intro n
    induction n with
    | zero =>
      change u∈tail m 1
      rw [first_tail_eq_top]
      trivial
    | succ n ih =>
      let h : ℤ := (n : ℤ)+1
      have hh : 0<h := by dsimp only [h];omega
      let x : tail m h := ⟨u,ih⟩
      have hx (t : (Field m)ˣ×(Field m)ˣ) : torusConjugate m h t x=x := by
        apply Subtype.ext
        apply Subtype.ext
        exact hfixed t
      have hzero := coordinate_eq_one_of_fixed_torus m hm h hh x hx
      have hnext := coordinateHom_kernel_le m h hh hzero
      change u∈tail m (h+1) at hnext
      simpa only [h,Nat.cast_succ,add_assoc] using hnext
  have hend := htail (rootHeightBound A)
  rw [terminal_tail_eq_bot,Subgroup.mem_bot] at hend
  exact hend

theorem eq_one_of_positive_diagonal_fixed (m : ℕ) (hm : 0<m)
    (u : originalModelFixed m) (hu : u∈fixedPositive m)
    (hfixed : ∀ d∈fixedDiagonal m,d*u*d⁻¹=u) : u=1 := by
  have he := positive_eq_one_of_fixed_torus m hm ⟨u,hu⟩ (fun t=>
    hfixed (fixedTorusHom m t) (fixedTorus_mem_diagonal m t.1 t.2))
  exact congrArg (fun x : fixedPositive m=>x.val) he

end SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveDiagonalCentralizer
