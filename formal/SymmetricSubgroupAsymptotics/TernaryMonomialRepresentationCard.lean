import SymmetricSubgroupAsymptotics.SeparatedEigenbasisMonomial
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-! An actual faithful representation permuting three ternary lines
embeds in six permutations times eight nonzero diagonal coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryMonomialRepresentationCard
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 3) V]

theorem card_le_fortyEight
    (rho : Representation (ZMod 3) G V) (hf : Function.Injective rho)
    (b : Module.Basis (Fin 3) (ZMod 3) V)
    (hmono : ∀ (g : G) (i : Fin 3),∃ (j : Fin 3) (c : ZMod 3),
      c≠0 ∧ rho g (b i)=c • b j) : Nat.card G≤48 := by
  choose p c hc he using hmono
  have hinj (g : G) : Function.Injective (p g) := by
    intro i j hij
    by_contra hne
    have hcancel : Function.Injective (rho g) := by
      intro v w hvw
      have hh := congrArg (rho g⁻¹) hvw
      have hh' : (rho g⁻¹*rho g) v=(rho g⁻¹*rho g) w := hh
      simpa only [←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh'
    have hcross : rho g (c g j • b i)=rho g (c g i • b j) := by
      rw [map_smul,map_smul,he,he,hij,smul_smul,smul_smul,mul_comm]
    have hsame := hcancel hcross
    have hz := congrArg (fun v : V => b.repr v i) hsame
    have hz' : c g j=0 := by
      simpa [Module.Basis.repr_self_apply,Ne.symm hne] using hz
    exact hc g j hz'
  let route (g : G) : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective (p g) ⟨hinj g,Finite.surjective_of_injective (hinj g)⟩
  let code : G → Equiv.Perm (Fin 3) × (Fin 3 → {a : ZMod 3 // a≠0}) :=
    fun g => (route g,fun i => ⟨c g i,hc g i⟩)
  have hcode : Function.Injective code := by
    intro g h hgh
    apply hf
    apply b.ext
    intro i
    have hp : p g i=p h i := congrArg (fun z => z.1 i) hgh
    have hcoeff : c g i=c h i := congrArg (fun z => (z.2 i).val) hgh
    rw [he,he,hp,hcoeff]
  have hbound := Nat.card_le_card_of_injective code hcode
  have hn : Fintype.card {a : ZMod 3 // a≠0}=2 := by decide +kernel
  have htarget : Nat.card (Equiv.Perm (Fin 3) × (Fin 3 → {a : ZMod 3 // a≠0}))=48 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_perm,Fintype.card_fun]
    norm_num [hn,Nat.factorial]
  exact htarget ▸ hbound

end SymmetricSubgroupAsymptotics.TernaryMonomialRepresentationCard
