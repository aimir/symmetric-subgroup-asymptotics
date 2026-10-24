import SymmetricSubgroupAsymptotics.BinaryPlanePermutationAffineEquiv

/-! A fixed-point-free involution on the four binary-plane points is a
literal translation. The proof uses the Klein-four missing-element
identity, not a permutation or subgroup enumeration. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFixedFreeInvolution
open BinaryPlanePermutationAffineEquiv

private theorem translation_formula (σ : Equiv.Perm Plane) (hsq : σ ^ 2 = 1)
    (hfree : ∀ v : Plane, σ v ≠ v) (v : Plane) : σ v + σ 0 = v := by
  have hh : σ * σ = 1 := by simpa only [pow_two] using hsq
  have hinv (x : Plane) : σ (σ x) = x :=
    congrArg (fun τ : Equiv.Perm Plane => τ x) hh
  by_cases hv0 : v = 0
  · subst v
    exact binaryVector_add_self (σ 0)
  by_cases hvσ : v = σ 0
  · rw [hvσ,hinv 0,zero_add]
  have hz0 : σ v ≠ 0 := by
    intro hz
    have he := congrArg σ hz
    rw [hinv v] at he
    exact hvσ he
  have hzσ : σ v ≠ σ 0 := fun he => hv0 (σ.injective he)
  have he : σ v = v + σ 0 :=
    IsAddKleinFour.eq_add_of_ne_all hv0 (hfree 0) hvσ hz0 (hfree v) hzσ
  rw [he,add_assoc,binaryVector_add_self,add_zero]

theorem linearPart_eq_one (σ : Equiv.Perm Plane) (hsq : σ ^ 2 = 1)
    (hfree : ∀ v : Plane, σ v ≠ v) : linearPart σ = 1 := by
  apply LinearEquiv.ext
  intro v
  exact translation_formula σ hsq hfree v

theorem subgroup_le_kernel (S : Subgroup (Equiv.Perm Plane))
    (hsq : ∀ s : S, s ^ 2 = 1)
    (hfree : ∀ s : S, s ≠ 1 → ∀ v : Plane, s.val v ≠ v) :
    S ≤ linearPart.ker := by
  intro s hs
  let u : S := ⟨s,hs⟩
  by_cases hu : u = 1
  · have hs1 : s = 1 := congrArg Subtype.val hu
    change linearPart s = 1
    rw [hs1,map_one]
  · apply MonoidHom.mem_ker.mpr
    exact linearPart_eq_one s (congrArg Subtype.val (hsq u)) (hfree u hu)

end SymmetricSubgroupAsymptotics.BinaryPlaneFixedFreeInvolution
