import SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights
import Mathlib.Algebra.Lie.Sl2

/-! A negative simple weight cannot be highest in a finite-dimensional
image of the actual original rational Serre algebra. Thus a nonzero
image remains nonzero under a single raising step at negative weight.
This uses an sl2 triple in the target and does not assume that the
original representation is faithful or that its source is finite. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreImageNegativeWeightRaising
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerreLocalNilpotence
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ)
variable {M:Type*} [LieRing M] [LieAlgebra ℚ M] [Module.Finite ℚ M]
local notation "L" => RationalLie A

theorem image_bracket_ne_zero_of_negative_weight (f:L→ₗ⁅ℚ⁆M)
    (neg:Bool) (i:Fin r) (hii:A i i=2) (v:L) (mu:ℚ)
    (hmu:mu<0) (hw:⁅coroot A neg i,v⁆=mu • v) (hv:f v≠0) :
    f ⁅rootVector A neg i,v⁆≠0 := by
  intro hz
  have hh:f (coroot A neg i)≠0 := by
    intro h
    have he:=congrArg f hw
    rw [LieHom.map_lie,h,zero_lie,map_smul] at he
    exact hv ((smul_eq_zero.mp he.symm).resolve_left (ne_of_lt hmu))
  have hf:⁅coroot A neg i,oppositeVector A neg i⁆=
      -(2 • oppositeVector A neg i) := by
    cases neg
    · change ⁅generator A (.H i),generator A (.F i)⁆= -(2 • generator A (.F i))
      simpa only [hii,two_smul] using generator_HF A i i
    · change ⁅-generator A (.H i),generator A (.E i)⁆= -(2 • generator A (.E i))
      rw [neg_lie,generator_HE,hii]
      simp only [two_smul]
  have ht:IsSl2Triple (f (coroot A neg i)) (f (rootVector A neg i))
      (f (oppositeVector A neg i)) :=
    { h_ne_zero:=hh
      lie_e_f:=by
        rw [←LieHom.map_lie,←lie_skew (rootVector A neg i) (oppositeVector A neg i),
          opposite_same,neg_neg]
      lie_h_e_nsmul:=by
        rw [←LieHom.map_lie,coroot_root,hii,map_smul]
        simp only [Int.cast_ofNat,two_smul]
      lie_h_f_nsmul:=by
        rw [←LieHom.map_lie,hf,map_neg,map_nsmul] }
  have hp:ht.HasPrimitiveVectorWith (f v) mu :=
    { ne_zero:=hv
      lie_h:=by rw [←LieHom.map_lie,hw,map_smul]
      lie_e:=by rw [←LieHom.map_lie,hz] }
  obtain ⟨n,hn⟩:=hp.exists_nat
  have hn0:(0:ℚ)≤n:=by exact_mod_cast Nat.zero_le n
  linarith

end SymmetricSubgroupAsymptotics.CFSGSerreImageNegativeWeightRaising
