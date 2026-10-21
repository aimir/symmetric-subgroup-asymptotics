import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialCycleGeneration
import SymmetricSubgroupAsymptotics.CFSGTypeARootTorus
import Mathlib.Data.ZMod.Basic

/-! A root element of parameter one and a signed coordinate cycle
already generate SL over every field whose cardinality equals its
characteristic. This uniform prime-field branch includes characteristics
two and three without a torus or a nonvanishing double commutator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeAPrimeFieldCycleGeneration
open CFSGTypeAElementaryMatrices CFSGTypeARootTorus
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F] [Finite F]

theorem all_parameters_of_one (p : ℕ) [CharP F p] (hcard : Nat.card F=p)
    (H : Subgroup (SL (n:=n) (F:=F))) {i j : n} (hij : i≠j)
    (hOne : elementary hij 1∈H) : ∀ a : F,elementary hij a∈H := by
  letI : Fintype F := Fintype.ofFinite F
  letI : NeZero p := ⟨by
    intro hp
    have hc := Nat.card_pos (α:=F)
    omega⟩
  have hc : Fintype.card F=p := by simpa only [Nat.card_eq_fintype_card] using hcard
  have hs := (ZMod.castHom_bijective F hc).2
  intro a
  obtain ⟨z,hz⟩ := hs a
  obtain ⟨k,rfl⟩ := ZMod.natCast_zmod_surjective z
  have he : (k : F)=a := by simpa only [map_natCast] using hz
  have hm := (rootAddParameters H hij).nsmul_mem hOne k
  change elementary hij (k • (1 : F))∈H at hm
  simpa only [nsmul_eq_mul,mul_one,he] using hm

/-- The literal root-one element and monomial cycle are an actual
uniform generating pair over every prime field, in all dimensions ≥2. -/
theorem eq_top_of_prime_field_edge (p : ℕ) [CharP F p] (hcard : Nat.card F=p)
    (hn : 2≤Fintype.card n)
    (σ : Equiv.Perm n) (hσ : σ.IsCycleOn (Finset.univ : Finset n))
    (W : SL (n:=n) (F:=F)) (d : n→F)
    (hW : W.val=CFSGTypeAMonomialMatrices.monomial σ d) (hd : ∀ k,d k≠0)
    (H : Subgroup (SL (n:=n) (F:=F))) (hHW : W∈H)
    (i : n) (hi : i≠σ.symm i) (hOne : elementary hi 1∈H) : H=⊤ := by
  exact CFSGTypeAMonomialCycleGeneration.eq_top_of_full_edge hn σ hσ W d hW hd H hHW
    i hi (all_parameters_of_one p hcard H hi hOne)

end SymmetricSubgroupAsymptotics.CFSGTypeAPrimeFieldCycleGeneration
