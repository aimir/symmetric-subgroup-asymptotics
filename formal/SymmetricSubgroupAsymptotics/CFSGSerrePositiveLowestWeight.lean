import SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights
import SymmetricSubgroupAsymptotics.CFSGSerreSimpleRootLocalNilpotence
import Mathlib.Algebra.Lie.Sl2

/-! A vector of positive simple weight killed by the opposite simple
adjoint is zero in the actual original rational Serre quotient. The
proof uses a point-dependent nilpotence exponent, not a finite-dimensional
or faithful-representation assumption. This permits sparse source root
identities to be verified from their lowerings and weights. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerrePositiveLowestWeight
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreSignedRootWeights
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ)
local notation "L" => RationalLie A

private theorem simple_sl2 (neg:Bool) (i:Fin r) (hii:A i i=2)
    (hne:coroot A neg i≠0) :
    IsSl2Triple (coroot A neg i) (rootVector A neg i) (oppositeVector A neg i) where
  h_ne_zero:=hne
  lie_e_f:=by
    rw [←lie_skew (rootVector A neg i) (oppositeVector A neg i),opposite_same,neg_neg]
  lie_h_e_nsmul:=by
    have h:=coroot_root A neg i i
    simpa only [hii,Int.cast_ofNat,two_smul] using h
  lie_h_f_nsmul:=by
    cases neg
    · change ⁅generator A (.H i),generator A (.F i)⁆= -(2 • generator A (.F i))
      simpa only [hii,two_smul] using generator_HF A i i
    · change ⁅-generator A (.H i),generator A (.E i)⁆= -(2 • generator A (.E i))
      rw [neg_lie,generator_HE,hii]
      simp only [two_smul]

theorem eq_zero_of_positive_weight_of_opposite_zero (neg:Bool) (i:Fin r)
    (hii:A i i=2) (v:L) (mu:ℚ) (hmu:0<mu)
    (hw:⁅coroot A neg i,v⁆=mu • v)
    (hf:⁅oppositeVector A neg i,v⁆=0) : v=0 := by
  by_contra hv
  have hh:coroot A neg i≠0 := by
    intro h
    have hz:mu • v=0 := by rw [←hw,h,zero_lie]
    exact hv ((smul_eq_zero.mp hz).resolve_left (ne_of_gt hmu))
  have ht:=simple_sl2 A neg i hii hh
  have P:ht.symm.HasPrimitiveVectorWith v (-mu) :=
    { ne_zero:=hv
      lie_h:=by rw [neg_lie,hw,neg_smul]
      lie_e:=hf }
  obtain ⟨N,hN⟩:=simpleRoot_ad_locally_nilpotent A neg i v
  have hzero:∃n:ℕ,(LieModule.toEnd ℚ L L (rootVector A neg i)^n) v=0 := ⟨N,hN⟩
  have hstart:(LieModule.toEnd ℚ L L (rootVector A neg i)^0) v≠0 := by
    simpa only [pow_zero,Module.End.one_apply] using hv
  obtain ⟨n,hn,hnext⟩:=Nat.exists_not_and_succ_of_not_zero_of_exists hstart hzero
  have he:=P.lie_e_pow_succ_toEnd_f n
  rw [hnext,lie_zero] at he
  have hn0:(0:ℚ)≤n:=by exact_mod_cast Nat.zero_le n
  have hc:((n:ℚ)+1)*(-mu-(n:ℚ))≠0 :=
    mul_ne_zero (by linarith) (by linarith)
  exact hn ((smul_eq_zero.mp he.symm).resolve_left hc)

end SymmetricSubgroupAsymptotics.CFSGSerrePositiveLowestWeight
