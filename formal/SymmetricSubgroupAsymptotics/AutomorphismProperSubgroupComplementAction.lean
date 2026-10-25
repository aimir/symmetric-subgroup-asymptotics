import SymmetricSubgroupAsymptotics.FourPointPermutationClassBound
import Mathlib.Algebra.Group.End

/-! A subgroup of automorphisms preserving a proper subgroup acts
faithfully on its literal complement. Agreement outside the subgroup
forces agreement inside by multiplying by one fixed outside element.
In particular, a complement with four points pays the proved S4 subgroup
class bound without recognizing a matrix stabilizer or enumerating it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AutomorphismProperSubgroupComplementAction

variable {N G : Type} [Group N] [Group G]

theorem eq_of_eq_on_complement (K : Subgroup N) (hK : K ≠ ⊤)
    (f g : MulAut N) (hfg : ∀ n : N, n ∉ K → f n = g n) : f = g := by
  have hex : ∃ a : N, a ∉ K := by
    by_contra hn
    apply hK
    apply top_unique
    intro a _
    by_contra ha
    exact hn ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  apply MulEquiv.ext
  intro n
  by_cases hn : n ∈ K
  · have han : a*n ∉ K := by
      intro h
      apply ha
      have hh := K.mul_mem h (K.inv_mem hn)
      simpa only [mul_inv_cancel_right] using hh
    have he := hfg (a*n) han
    rw [map_mul, map_mul, hfg a ha] at he
    exact mul_left_cancel he
  · exact hfg n hn

def complementHom (K : Subgroup N) (ρ : G →* MulAut N)
    (hstable : ∀ (g : G) (n : N), ρ g n ∈ K ↔ n ∈ K) :
    G →* Equiv.Perm {n : N // n ∉ K} where
  toFun g := (ρ g).toEquiv.subtypeEquiv (fun n => (not_congr (hstable g n)).symm)
  map_one' := by
    apply Equiv.ext
    intro n
    apply Subtype.ext
    change ρ 1 n.val = n.val
    simp only [map_one, MulAut.one_apply]
  map_mul' g h := by
    apply Equiv.ext
    intro n
    apply Subtype.ext
    change ρ (g*h) n.val = ρ g (ρ h n.val)
    simp only [map_mul, MulAut.mul_apply]

theorem complementHom_injective (K : Subgroup N) (hK : K ≠ ⊤)
    (ρ : G →* MulAut N) (hρ : Function.Injective ρ)
    (hstable : ∀ (g : G) (n : N), ρ g n ∈ K ↔ n ∈ K) :
    Function.Injective (complementHom K ρ hstable) := by
  intro g h he
  apply hρ
  apply eq_of_eq_on_complement K hK
  intro n hn
  exact congrArg
    (fun e : Equiv.Perm {n : N // n ∉ K} => (e ⟨n, hn⟩).val) he

theorem class_card_le_five_of_complement_card_four [Finite N] [Finite G]
    (K : Subgroup N) (hK : K ≠ ⊤)
    (ρ : G →* MulAut N) (hρ : Function.Injective ρ)
    (hstable : ∀ (g : G) (n : N), ρ g n ∈ K ↔ n ∈ K)
    (hcard : Nat.card {n : N // n ∉ K} = 4) : Nat.card (ConjClasses G) ≤ 5 := by
  let ePoint : {n : N // n ∉ K} ≃ Fin 4 := Finite.equivFinOfCardEq hcard
  let f := ePoint.permCongrHom.toMonoidHom.comp (complementHom K ρ hstable)
  have hf : Function.Injective f := ePoint.permCongrHom.injective.comp
    (complementHom_injective K hK ρ hρ hstable)
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  have he : Nat.card (ConjClasses G) ≤ Nat.card (ConjClasses f.range) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact he.trans (FourPointPermutationClassBound.subgroup_class_card_le_five f.range)

end SymmetricSubgroupAsymptotics.AutomorphismProperSubgroupComplementAction
