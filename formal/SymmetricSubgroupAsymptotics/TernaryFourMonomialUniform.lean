import SymmetricSubgroupAsymptotics.TernaryMonomialTransitiveMaschkeUniform
import SymmetricSubgroupAsymptotics.SylowPrimePowerTransitive

/-! Every transitive monomial action on four ternary coordinates has
uniform generator bound one. The actual Sylow2 restriction is transitive,
and its order is invertible in F3. All signs remain coordinate dependent. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourMonomialUniform

theorem uniform
    {R : Type} [Group R] [Finite R]
    (b : R →* Equiv.Perm (Fin 4)) (d : R → Fin 4 → ZMod 3)
    (hone : ∀ i, d 1 i = 1)
    (hmul : ∀ g h i, d (g*h) i = d g i * d h (b g⁻¹ i))
    (htrans : ∀ x y : Fin 4, ∃ g : R, b g x = y) :
    UniformSubrepresentationGeneratorBound
      (TernaryMonomialOrbitUniform.representation b d hone hmul) 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction R (Fin 4) := MulAction.compHom (Fin 4) b
  letI : MulAction.IsPretransitive R (Fin 4) := ⟨htrans⟩
  let P : Sylow 2 R := Classical.choice inferInstance
  have hP : MulAction.IsPretransitive P (Fin 4) :=
    sylow_isPretransitive_of_card_eq_prime_pow (a := 2) P (by norm_num)
  letI : NeZero (Nat.card P : ZMod 3) := ⟨by
    obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn,Nat.cast_pow]
    exact pow_ne_zero _ (by decide : (2 : ZMod 3) ≠ 0)⟩
  let bp : P →* Equiv.Perm (Fin 4) := b.comp (P : Subgroup R).subtype
  let dp : P → Fin 4 → ZMod 3 := fun g => d g
  have hpone : ∀ i, dp 1 i = 1 := hone
  have hpmul : ∀ g h i, dp (g*h) i = dp g i * dp h (bp g⁻¹ i) :=
    fun g h i => hmul g h i
  apply UniformSubrepresentationGeneratorBound.of_comp
    (TernaryMonomialOrbitUniform.representation b d hone hmul) (P : Subgroup R).subtype
  change UniformSubrepresentationGeneratorBound
    (TernaryMonomialOrbitUniform.representation bp dp hpone hpmul) 1
  apply TernaryMonomialTransitiveMaschkeUniform.uniform_of_invertible_order
    bp dp hpone hpmul (fun _ : Fin 1 => (0 : Fin 4))
  intro x
  obtain ⟨g,hg⟩ := hP.exists_smul_eq (0 : Fin 4) x
  exact ⟨0,g,hg⟩

end SymmetricSubgroupAsymptotics.TernaryFourMonomialUniform
