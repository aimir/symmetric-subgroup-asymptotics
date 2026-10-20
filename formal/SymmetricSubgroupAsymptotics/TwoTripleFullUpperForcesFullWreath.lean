import SymmetricSubgroupAsymptotics.TwoTripleBinaryUpperRecognition
import SymmetricSubgroupAsymptotics.TwoTripleTernaryKernelIrreducible
import SymmetricSubgroupAsymptotics.TernaryLocalWreathNormalGenerators

/-! Full binary upper and a nonzero actual ternary kernel force the full
two-triple wreath. Offset binary lifts are retained. The algebraic proof
uses independent sign and swap invariance, not a list of subgroups. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwoTripleFullUpperForcesFullWreath
open SemidirectProduct
abbrev Binary := Multiplicative (ZMod 2)
abbrev Vector := TwoTripleTernaryKernelIrreducible.Vector
abbrev Local := TernaryLocalWreathNormalGenerators.Local
abbrev Model := TernaryLocalWreathNormalGenerators.Model
abbrev Upper := TwoTripleBinaryUpperRecognition.Upper

private def modelCoordinates : Model ≃ (Vector × (Binary × Binary)) × Binary where
  toFun g := (((g.left.1.left.toAdd,g.left.2.left.toAdd),(g.left.1.right,g.left.2.right)),g.right)
  invFun p := ⟨(⟨Multiplicative.ofAdd p.1.1.1,p.1.2.1⟩,
    ⟨Multiplicative.ofAdd p.1.1.2,p.1.2.2⟩),p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
local instance : Fintype Model := Fintype.ofEquiv ((Vector × (Binary × Binary)) × Binary) modelCoordinates.symm
local instance : DecidableEq Model := fun a b =>
  decidable_of_iff (modelCoordinates a = modelCoordinates b) modelCoordinates.injective.eq_iff
private def upperCoordinates : Upper ≃ (Binary × Binary) × Binary where
  toFun g := (g.left,g.right)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
local instance : DecidableEq Upper := fun a b =>
  decidable_of_iff (upperCoordinates a = upperCoordinates b) upperCoordinates.injective.eq_iff

def upper : Model →* Upper := C2Wreath.mapLocal (rightHom : Local →* Binary)
def translation : Multiplicative Vector →* Model where
  toFun v := inl (inl (Multiplicative.ofAdd v.toAdd.1),inl (Multiplicative.ofAdd v.toAdd.2))
  map_one' := by decide +kernel
  map_mul' := by intro v w; revert v w; decide +kernel

private theorem translation_zero : translation (Multiplicative.ofAdd (0 : Vector)) = 1 := by decide +kernel
private theorem translation_kernel : ∀ g : Model, upper g = 1 →
    ∃ v : Vector, translation (Multiplicative.ofAdd v) = g := by decide +kernel

def signUpper : Upper := inl (C2Wreath.gen,1)
def swapUpper : Upper := inr C2Wreath.gen
private theorem conjugate_sign : ∀ (g : Model) (v : Vector), upper g = signUpper →
    g * translation (Multiplicative.ofAdd v) * g⁻¹ =
      translation (Multiplicative.ofAdd (TwoTripleTernaryKernelIrreducible.flip v)) := by decide +kernel
private theorem conjugate_swap : ∀ (g : Model) (v : Vector), upper g = swapUpper →
    g * translation (Multiplicative.ofAdd v) * g⁻¹ =
      translation (Multiplicative.ofAdd (TwoTripleTernaryKernelIrreducible.swap v)) := by decide +kernel

def translationSpace (H : Subgroup Model) : AddSubgroup Vector where
  carrier := {v | translation (Multiplicative.ofAdd v) ∈ H}
  zero_mem' := by
    change translation (Multiplicative.ofAdd (0 : Vector)) ∈ H
    rw [translation_zero]
    exact H.one_mem
  add_mem' := by
    intro v w hv hw
    change translation (Multiplicative.ofAdd v * Multiplicative.ofAdd w) ∈ H
    rw [map_mul]
    exact H.mul_mem hv hw
  neg_mem' := by
    intro v hv
    change translation (Multiplicative.ofAdd v)⁻¹ ∈ H
    rw [map_inv]
    exact H.inv_mem hv

theorem eq_top_of_full_upper_nonzero_kernel (H : Subgroup Model)
    (hfull : ∀ u : Upper, ∃ g : Model, g ∈ H ∧ upper g = u)
    (hne : ∃ g : Model, g ∈ H ∧ upper g = 1 ∧ g ≠ 1) : H = ⊤ := by
  let A := translationSpace H
  have hAne : A ≠ ⊥ := by
    obtain ⟨g,hg,hupper,hgne⟩ := hne
    obtain ⟨v,hv⟩ := translation_kernel g hupper
    intro hbot
    have hvmem : v ∈ A := by change translation (Multiplicative.ofAdd v) ∈ H; rwa [hv]
    rw [hbot] at hvmem
    have hvzero : v = 0 := AddSubgroup.mem_bot.mp hvmem
    apply hgne
    rw [← hv,hvzero,translation_zero]
  obtain ⟨s,hs,hsupper⟩ := hfull signUpper
  obtain ⟨t,ht,htupper⟩ := hfull swapUpper
  have hA : A = ⊤ := by
    apply TwoTripleTernaryKernelIrreducible.eq_top_of_sign_swap A hAne
    · intro v hv
      change translation (Multiplicative.ofAdd (TwoTripleTernaryKernelIrreducible.flip v)) ∈ H
      rw [← conjugate_sign s v hsupper]
      exact H.mul_mem (H.mul_mem hs hv) (H.inv_mem hs)
    · intro v hv
      change translation (Multiplicative.ofAdd (TwoTripleTernaryKernelIrreducible.swap v)) ∈ H
      rw [← conjugate_swap t v htupper]
      exact H.mul_mem (H.mul_mem ht hv) (H.inv_mem ht)
  apply top_unique
  intro g _
  obtain ⟨h,hh,hupper⟩ := hfull (upper g)
  have hdiff : upper (g*h⁻¹) = 1 := by rw [map_mul,map_inv,hupper,mul_inv_cancel]
  obtain ⟨v,hv⟩ := translation_kernel (g*h⁻¹) hdiff
  have hvmem : v ∈ A := by rw [hA]; exact AddSubgroup.mem_top _
  have hmem : g*h⁻¹ ∈ H := by rw [← hv]; exact hvmem
  simpa only [inv_mul_cancel_right] using H.mul_mem hmem hh

end SymmetricSubgroupAsymptotics.TwoTripleFullUpperForcesFullWreath
