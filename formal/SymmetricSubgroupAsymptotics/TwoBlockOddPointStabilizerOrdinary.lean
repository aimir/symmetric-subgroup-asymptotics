import SymmetricSubgroupAsymptotics.PrimitiveTwoCoordinateOddKernelOrdinary
import SymmetricSubgroupAsymptotics.TwoBlockWreathNormalGenerators

/-! A two-block source with odd original point stabilizers retains an
injective local coordinate whenever its actual primitive component has
even degree. The coordinate kernel is embedded in an original physical
point stabilizer using the supplied literal equivariant block chart. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwoBlockOddPointStabilizerOrdinary
open PermutationalWreathProduct TwoBlockWreathNormalGenerators

variable {G L Q I Y Omega : Type} [Group G] [Group L] [Group Q]
    [MulAction Q I] [MulAction L Y] [MulAction G Omega]
    (rho : G →* PermutationalWreathProduct L Q I)
    (e : Y × I ≃ Omega)
    (hcompat : ∀ (a : G) (p : Y × I), e (rho a • p) = a • e p)

def coordinateKernelToStabilizer (i : I) (y : Y) :
    (coordinate rho i).ker →* MulAction.stabilizer G (e (y,i)) where
  toFun x := ⟨((x : (top rho).ker) : G),by
    have hright : (rho (((x : (top rho).ker) : G))).right = 1 :=
      (x : (top rho).ker).property
    have hleft : (rho (((x : (top rho).ker) : G))).left i = 1 := x.property
    change (((x : (top rho).ker) : G)) • e (y,i) = e (y,i)
    rw [←hcompat]
    simp only [smul_def,hright,one_smul,hleft]⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' x z := by apply Subtype.ext; rfl

theorem coordinateKernelToStabilizer_injective (i : I) (y : Y) :
    Function.Injective (coordinateKernelToStabilizer rho e hcompat i y) := by
  intro x z h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun a : MulAction.stabilizer G (e (y,i)) => (a : G)) h

variable [Finite G] [Finite L] [Finite Q] [Fintype I] [Finite Y] [Nonempty Y]
    [FaithfulSMul Q I] [FaithfulSMul L Y] [MulAction.IsPreprimitive L Y]

include e hcompat in
theorem genRank_le_local_add_top (hI : Nat.card I = 2)
    (hrho : Function.Injective rho) (htop : Function.Surjective (top rho))
    (hfull : Compression.FullComponent rho) (heven : 2 ∣ Nat.card Y)
    (hodd : ∀ x : Omega, ¬2 ∣ Nat.card (MulAction.stabilizer G x)) :
    MarkedC4.genRank G ≤ MarkedC4.genRank L + MarkedC4.genRank Q := by
  let r : I ≃ Fin 2 := Finite.equivFinOfCardEq hI
  let i₀ : I := r.symm 0
  let i₁ : I := r.symm 1
  let N := (top rho).ker
  let f : N →* L := coordinate rho i₀
  let g : N →* L := coordinate rho i₁
  have hjoint : Function.Injective (fun x : N => (f x,g x)) := by
    intro x z hz
    apply coordinates_joint_injective rho hrho
    funext i
    have hi : i = r.symm (r i) := (r.symm_apply_apply i).symm
    rw [hi]
    have h0 := congrArg Prod.fst hz
    have h1 := congrArg Prod.snd hz
    generalize r i = j
    fin_cases j
    · exact h0
    · exact h1
  let y : Y := Classical.choice inferInstance
  have hdiv : Nat.card f.ker ∣ Nat.card (MulAction.stabilizer G (e (y,i₀))) :=
    Subgroup.card_dvd_of_injective (coordinateKernelToStabilizer rho e hcompat i₀ y)
      (coordinateKernelToStabilizer_injective rho e hcompat i₀ y)
  have hkerodd : ¬2 ∣ Nat.card f.ker := fun h => hodd _ (h.trans hdiv)
  have hh := PrimitiveTwoCoordinateOddKernelOrdinary.genRank_le_local_add_quotient
    (X := Y) N f g (coordinate_surjective rho hI hfull i₀)
      (coordinate_surjective rho hI hfull i₁) hjoint heven hkerodd
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv
    (QuotientGroup.quotientKerEquivOfSurjective (top rho) htop)] at hh
  exact hh

end SymmetricSubgroupAsymptotics.TwoBlockOddPointStabilizerOrdinary
