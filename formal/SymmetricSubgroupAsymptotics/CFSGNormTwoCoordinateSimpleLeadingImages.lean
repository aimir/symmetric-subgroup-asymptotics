import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLeadingAxes
import SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxes

/-! The first-layer image of the actual simple-root subgroup IS the
entire corresponding coordinate axis, with no parameter or field-size
restriction. Non-simple root subgroups have trivial first-layer image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleLeadingImages
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoCoordinateRootLeadingAxes CFSGSimpleCoordinateAxes
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem simple_root_leading_image (K : Type) [Field K] (i : Fin r) :
    ((rootSubgroup A hd hs hp ho K (s₀ i)).subgroupOf (PositiveGroup A hd hs hp ho K)).map
      (leadingHom A hd hs hp ho K)=axis (K:=K) i := by
  obtain ⟨ε,hε,he⟩ := leading_selected_simple A hd hs hp ho i
  have hεsq : (ε:K)*(ε:K)=1 := by rcases hε with rfl|rfl <;> norm_num
  have hpos : ∀j,0≤(s₀ i : Roots A).val j := by
    intro j
    change 0≤(Pi.single i (1:ℤ) : Fin r→ℤ) j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  apply Subgroup.ext
  intro c
  constructor
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨a,ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K (s₀ i) u.val).mp hu
    apply (mem_axis_iff i _).mpr
    refine ⟨(ε:K)*a,?_⟩
    change Multiplicative.ofAdd (Pi.single i ((ε:K)*a) : Fin r→K)=
      Multiplicative.ofAdd (leadingCoordinates A hd hs hp ho K u.val)
    rw [←ha,he K a]
  · intro hc
    obtain ⟨a,rfl⟩ := (mem_axis_iff i c).mp hc
    let u := positiveRootParameterHom A hd hs hp ho K (s₀ i) hpos (Multiplicative.ofAdd ((ε:K)*a))
    refine ⟨u,selectedRootElement_mem A hd hs hp ho K (s₀ i) ((ε:K)*a),?_⟩
    change Multiplicative.ofAdd (leadingCoordinates A hd hs hp ho K
      (selectedRootElement A hd hs hp ho K (s₀ i) ((ε:K)*a)))=
        Multiplicative.ofAdd (Pi.single i a : Fin r→K)
    rw [he K ((ε:K)*a),←mul_assoc,hεsq,one_mul]

theorem nonsimple_root_leading_image (K : Type) [Field K] (k : Roots A)
    (hk : ∀i : Fin r,k≠(s₀ i : Roots A)) :
    ((rootSubgroup A hd hs hp ho K k).subgroupOf (PositiveGroup A hd hs hp ho K)).map
      (leadingHom A hd hs hp ho K)=⊥ := by
  apply le_antisymm _ bot_le
  rintro c ⟨u,hu,rfl⟩
  apply Subgroup.mem_bot.mpr
  obtain ⟨a,ha⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k u.val).mp hu
  change Multiplicative.ofAdd (leadingCoordinates A hd hs hp ho K u.val)=1
  rw [←ha,leading_selected_nonsimple A hd hs hp ho K k hk a]
  rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleLeadingImages
