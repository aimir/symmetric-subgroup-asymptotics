import SymmetricSubgroupAsymptotics.SixPairB6CubicPointStabilizer
import SymmetricSubgroupAsymptotics.SixPairB6CubicOrbitCoordinates
import SymmetricSubgroupAsymptotics.BinaryPairSubgroupCuts
import SymmetricSubgroupAsymptotics.CubicKernelCoordinateEnvelope

/-! Canonical joint cubic coordinates from the ORIGINAL transitive
12-point action. Its actual point stabilizer gives a rank2 local
observation; the three original conjugates separate by faithfulness.
There is no literal point chart, enumeration or coordinate-bound premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SixPairB6CubicActualCoordinates

variable {U : Subgroup (Equiv.Perm (Fin 12))}
    (top : U →* CyclicThree) (htop : Function.Surjective top)
    (A : Rep (ZMod 2) CyclicThree) (E : OriginalKernelModuleChart top A)

include E in
theorem kernel_binary : IsPGroup 2 top.ker :=
  (ZModModule.isPGroup_multiplicative (n := 2) (G := A)).of_injective
    E.equiv.symm.toMonoidHom E.equiv.symm.injective

include E in
theorem module_finite : Finite A :=
  Finite.of_equiv top.ker (E.equiv.symm.toEquiv.trans Multiplicative.toAdd)

abbrev stabilizerCut : Subgroup top.ker :=
  (MulAction.stabilizer U (0 : Fin 12)).subgroupOf top.ker

include top E in
def localSpace : Submodule (ZMod 2) A :=
  sectionSubgroupImage (p := 2) E.equiv.symm.toMonoidHom (stabilizerCut top)

include E in
private theorem chart_kernel_le_cut : E.equiv.symm.toMonoidHom.ker ≤ stabilizerCut top := by
  intro k hk
  have he : E.equiv.symm k = 1 := hk
  have hk1 : k = 1 := E.equiv.symm.injective (he.trans E.equiv.symm.map_one.symm)
  rw [hk1]
  exact (stabilizerCut top).one_mem

/-- Membership in the local vector cut is EXACT original point fixing. -/
theorem localSpace_mem_iff (v : A) : v ∈ localSpace top A E ↔
    (E.equiv (Multiplicative.ofAdd v) : U) ∈ MulAction.stabilizer U (0 : Fin 12) := by
  have h := sectionSubgroupImage_mem_iff (p := 2) E.equiv.symm.toMonoidHom
    (stabilizerCut top) (chart_kernel_le_cut top A E)
    (E.equiv (Multiplicative.ofAdd v))
  change (E.equiv.symm (E.equiv (Multiplicative.ofAdd v))).toAdd ∈
      localSpace top A E ↔
    (E.equiv (Multiplicative.ofAdd v) : U) ∈
      MulAction.stabilizer U (0 : Fin 12) at h
  simpa only [MulEquiv.symm_apply_apply,toAdd_ofAdd] using h

variable [MulAction.IsPretransitive U (Fin 12)]

include htop E in
/-- The actual local quotient has four elements, from the original
stabilizer index; no stored row profile is used. -/
theorem local_quotient_card_four : Nat.card (A ⧸ localSpace top A E) = 4 := by
  letI : Finite A := module_finite top A E
  let f := sectionSubgroupCutMap (p := 2) E.equiv.symm.toMonoidHom (stabilizerCut top)
  have hf : Function.Surjective f := sectionSubgroupCutMap_surjective (p := 2)
    E.equiv.symm.toMonoidHom E.equiv.symm.surjective (stabilizerCut top)
  have hk : f.ker = stabilizerCut top := sectionSubgroupCutMap_ker (p := 2)
    E.equiv.symm.toMonoidHom (stabilizerCut top) (chart_kernel_le_cut top A E)
  have hi : f.ker.index = Nat.card (Multiplicative (A ⧸ localSpace top A E)) := by
    rw [Subgroup.index_ker,f.range_eq_top_of_surjective hf,Subgroup.card_top]
    rfl
  rw [hk] at hi
  have hfour : (stabilizerCut top).index = 4 :=
    SixPairB6CubicPointStabilizer.stabilizer_relative_index_four
      top htop (kernel_binary top A E) 0
  exact (Nat.card_congr (Multiplicative.toAdd)).symm.trans (hi.symm.trans hfour)

include htop in
/-- Choose coordinates ONLY on the actual four-element local quotient. -/
def localChart : (A ⧸ localSpace top A E) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) := by
  letI : Finite A := module_finite top A E
  have hc : Nat.card (A ⧸ localSpace top A E) =
      2 ^ Module.finrank (ZMod 2) (A ⧸ localSpace top A E) := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A ⧸ localSpace top A E))
  have hp : 2 ^ Module.finrank (ZMod 2) (A ⧸ localSpace top A E) = 2^2 :=
    hc.symm.trans (local_quotient_card_four top htop A E)
  have hd := Nat.pow_right_injective (by decide : 1 < 2) hp
  exact LinearEquiv.ofFinrankEq _ _ (by rw [hd]; simp)

include top htop E in
def observation : A →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  (localChart top htop A E).toLinearMap.comp (localSpace top A E).mkQ

/-- Zero observation is equivalent to fixing the original selected point. -/
theorem observation_eq_zero_iff (v : A) : observation top htop A E v = 0 ↔
    (E.equiv (Multiplicative.ofAdd v) : U) ∈ MulAction.stabilizer U (0 : Fin 12) := by
  change localChart top htop A E ((localSpace top A E).mkQ v) = 0 ↔ _
  rw [(localChart top htop A E).map_eq_zero_iff]
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact localSpace_mem_iff top A E v

include htop E in
/-- The same actual point stabilizer has trivial original core. This
proves separation by the three cubic translates without an independent
module multiplicity assumption. -/
theorem observations_separate (v : A)
    (hv : ∀ c : CyclicThree, observation top htop A E (A.ρ c v) = 0) : v = 0 := by
  let k : U := E.equiv (Multiplicative.ofAdd v)
  have hfix : ∀ y : Fin 12, k • y = y := by
    intro y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq U (0 : Fin 12) y
    have hm := (observation_eq_zero_iff top htop A E (A.ρ (top g⁻¹) v)).mp (hv (top g⁻¹))
    have hc : g⁻¹*k*g ∈ MulAction.stabilizer U (0 : Fin 12) := by
      simpa only [E.conjugate,inv_inv] using hm
    have hz : (g⁻¹*k*g) • (0 : Fin 12) = 0 := MulAction.mem_stabilizer_iff.mp hc
    have he := congrArg (fun x : Fin 12 => g • x) hz
    have he' : k • (g • (0 : Fin 12)) = g • (0 : Fin 12) := by
      simpa only [mul_smul,smul_inv_smul] using he
    rwa [hg] at he'
  have hk : k = 1 := by
    apply eq_of_smul_eq_smul (α := Fin 12)
    intro y
    exact (hfix y).trans (one_smul U y).symm
  have hk' : E.equiv (Multiplicative.ofAdd v) = 1 := Subtype.ext hk
  have hv' : Multiplicative.ofAdd v = 1 :=
    E.equiv.injective (hk'.trans E.equiv.map_one.symm)
  exact congrArg Multiplicative.toAdd hv'

include top htop E in
/-- Joint invariant/twisted chart forced by the original action geometry. -/
def coordinates : CubicBinaryCoordinates A.ρ :=
  SixPairB6CubicOrbitCoordinates.coordinates A.ρ (observation top htop A E)
    (observations_separate top htop A E)

end SixPairB6CubicActualCoordinates
end SymmetricSubgroupAsymptotics
end
