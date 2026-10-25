import SymmetricSubgroupAsymptotics.PermutationalWreathFinite
import Mathlib.GroupTheory.Index

/-! A genuinely saturated base and a surjective SAME top make an
injective wreath embedding onto. This is an actual group equivalence,
not a class comparison with a larger base or a splitting assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathFullBaseSaturation

variable {A C Q I : Type} [Group A] [Group C] [Group Q] [MulAction Q I]
    [Finite A] [Finite C] [Finite Q] [Finite I]

theorem surjective_of_kernel_card
    (rho : A →* PermutationalWreathProduct C Q I) (hi : Function.Injective rho)
    (htop : Function.Surjective (PermutationalWreathProduct.rightHom.comp rho))
    (hbase : Nat.card (PermutationalWreathProduct.rightHom.comp rho).ker =
      Nat.card C ^ Nat.card I) : Function.Surjective rho := by
  let f : A →* Q := PermutationalWreathProduct.rightHom.comp rho
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.mpr htop
  have hrc : Nat.card f.range = Nat.card Q := by
    rw [hr]
    exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).toEquiv
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker,hrc] at hc
  have he : Nat.card A = Nat.card (PermutationalWreathProduct C Q I) := by
    calc
      Nat.card A = Nat.card f.ker * Nat.card Q := hc.symm
      _ = Nat.card C ^ Nat.card I * Nat.card Q := by rw [hbase]
      _ = _ := PermutationalWreathProduct.natCard_eq.symm
  exact ((Nat.bijective_iff_injective_and_card rho).mpr ⟨hi,he⟩).surjective

def fullWreathEquivOfKernelCard
    (rho : A →* PermutationalWreathProduct C Q I) (hi : Function.Injective rho)
    (htop : Function.Surjective (PermutationalWreathProduct.rightHom.comp rho))
    (hbase : Nat.card (PermutationalWreathProduct.rightHom.comp rho).ker =
      Nat.card C ^ Nat.card I) : A ≃* PermutationalWreathProduct C Q I :=
  MulEquiv.ofBijective rho ⟨hi,surjective_of_kernel_card rho hi htop hbase⟩

end SymmetricSubgroupAsymptotics.WreathFullBaseSaturation
