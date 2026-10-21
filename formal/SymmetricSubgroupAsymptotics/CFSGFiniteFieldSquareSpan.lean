import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Additive generation by scaled squares in a finite field. This is the
scalar step in actual elementary-root extraction; it does not enumerate
field elements or assume a two-generation theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareSpan
variable {F : Type*} [Field F] [Finite F]

/-- All scaled squares additively span the entire finite field. In odd
characteristic use a difference of two squares; in characteristic two
use injectivity, hence surjectivity, of squaring. -/
theorem eq_top_of_scaled_squares (B : AddSubgroup F) (m : F) (hm : m≠0)
    (hB : ∀ t : F,m*t^2∈B) : B=⊤ := by
  apply top_unique
  intro a _
  by_cases hTwo : (2 : F)=0
  · have hi : Function.Injective (fun t : F => t^2) := by
      intro x y he
      change x^2=y^2 at he
      have hz : (x-y)^2=0 := by
        calc
          (x-y)^2 = x^2+y^2 := by ring_nf;simp [hTwo]
          _ = 0 := by rw [he,←two_mul,hTwo,zero_mul]
      have hz' : (x-y)*(x-y)=0 := by simpa only [pow_two] using hz
      rcases mul_eq_zero.mp hz' with h|h
      · exact sub_eq_zero.mp h
      · exact sub_eq_zero.mp h
    obtain ⟨t,ht⟩ := Finite.surjective_of_injective hi (a/m)
    change t^2=a/m at ht
    have he : m*t^2=a := by rw [ht];field_simp [hm]
    exact he ▸ hB t
  · let u := (a/m+1)/2
    let v := (a/m-1)/2
    have he : m*u^2-m*v^2=a := by
      dsimp [u,v]
      field_simp [hm,hTwo] <;> ring
    exact he ▸ B.sub_mem (hB u) (hB v)

/-- Conjugation scalars that are squares of a multiplicative generator
already suffice to generate an entire additive root group. -/
theorem eq_top_of_scaled_even_powers (B : AddSubgroup F) (g : Fˣ)
    (hg : ∀ u : Fˣ,u∈Subgroup.zpowers g) (m : F) (hm : m≠0)
    (hB : ∀ k : ℕ,m*(g : F)^(2*k)∈B) : B=⊤ := by
  apply eq_top_of_scaled_squares B m hm
  intro t
  by_cases ht : t=0
  · simpa only [ht,zero_pow (by decide : 2≠0),mul_zero] using B.zero_mem
  let u : Fˣ := Units.mk0 t ht
  obtain ⟨k,hk⟩ : u∈Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr (hg u)
  have hv : (g : F)^k=t := by
    simpa only [Units.val_pow_eq_pow_val,Units.val_mk0,u] using congrArg (fun v : Fˣ => (v : F)) hk
  have he : m*(g : F)^(2*k)=m*t^2 := by rw [Nat.mul_comm 2 k,pow_mul,hv]
  exact he ▸ hB k

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareSpan
