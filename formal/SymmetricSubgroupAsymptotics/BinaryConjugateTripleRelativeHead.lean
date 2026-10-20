import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters

/-! A literal conjugate-triple norm identity kills the complete binary
relative head. This retains the actual normal subgroup and conjugation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem binary_relativeHead_eq_zero_of_conjugate_triple
    (g : G)
    (hnorm : ∀ n : N,
      n * MulAut.conjNormal g n * MulAut.conjNormal g (MulAut.conjNormal g n) = 1) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) = 0 := by
  have hzero (chi : primeRelativeCharacters 2 N) (n : N) :
      chi.1 (Additive.ofMul n) = 0 := by
    have hinv (m : N) :
        chi.1 (Additive.ofMul (MulAut.conjNormal g m)) =
          chi.1 (Additive.ofMul m) := chi.2 g m
    have h := congrArg (fun m : N => chi.1 (Additive.ofMul m)) (hnorm n)
    change chi.1 ((Additive.ofMul n + Additive.ofMul (MulAut.conjNormal g n)) +
      Additive.ofMul (MulAut.conjNormal g (MulAut.conjNormal g n))) = chi.1 0 at h
    simp only [map_add, map_zero, hinv] at h
    have htwo : chi.1 (Additive.ofMul n) + chi.1 (Additive.ofMul n) = 0 := by
      have ht := add_smul (1 : ZMod 2) 1 (chi.1 (Additive.ofMul n))
      simpa only [show (1 : ZMod 2) + 1 = 0 from by decide, zero_smul, one_smul] using ht.symm
    simpa only [htwo, zero_add] using h
  letI : Subsingleton (primeRelativeCharacters 2 N) := ⟨by
    intro chi psi
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro n
    exact (hzero chi n.toMul).trans (hzero psi n.toMul).symm⟩
  exact Module.finrank_zero_of_subsingleton

end SymmetricSubgroupAsymptotics
