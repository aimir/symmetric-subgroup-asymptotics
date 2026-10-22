import SymmetricSubgroupAsymptotics.CFSGLinearCentralizerTransport
import SymmetricSubgroupAsymptotics.CFSGIsotypicCentralizerBinaryTwo

/-! Soluble centralizers on the original binary carrier, in the two
constituent configurations relevant in dimension six. The actual chart
and its equivariance are retained; no six-dimensional subgroup catalogue
or extra solvability input is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGIsotypicCentralizerOriginalSix
open CFSGIrreducibleLinearCentralizer CFSGIsotypicCentralizerMultiplicity

theorem original_twofold_centralizer_soluble
    {S V W : Type} [Group S] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
    [FiniteDimensional (ZMod 2) W]
    (rho : Representation (ZMod 2) S V) (tau : Representation (ZMod 2) S W)
    (e : V ≃ₗ[ZMod 2] (Fin 2 → W))
    (he : ∀ s v i, e (rho s v) i = tau s (e v i))
    (hirr : Representation.IsIrreducible tau) (hf : Function.Injective tau)
    (hnc : ¬ IsMulCommutative S) (hd : Module.finrank (ZMod 2) W = 3) :
    IsSolvable (linearCentralizer rho) := by
  letI : IsSolvable (linearCentralizer (repeated (I:=Fin 2) tau)) :=
    CFSGIsotypicCentralizerBinaryTwo.binary_twofold_centralizer_soluble tau hirr hf hnc hd
  apply CFSGLinearCentralizerTransport.solvable_of_chart rho (repeated tau) e
  intro s v
  funext i
  exact he s v i

private theorem soluble_of_card_dvd_sixtyThree
    {H : Type} [Group H] [Finite H] (hc : Nat.card H ∣ 63) : IsSolvable H := by
  have hlist : ∀ n ∈ Nat.divisors 63,
      n=1 ∨ n=3 ∨ n=7 ∨ n=9 ∨ n=21 ∨ n=63 := by decide +kernel
  have hh := hlist _ (Nat.mem_divisors.mpr ⟨hc,by decide⟩)
  rcases hh with h|h|h|h|h|h
  · exact burnsideTwoPrimeSolvability.solvable H 3 7 0 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable H 3 7 1 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable H 3 7 0 1 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable H 3 7 2 0 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable H 3 7 1 1 (by decide) (by decide) (by norm_num [h])
  · exact burnsideTwoPrimeSolvability.solvable H 3 7 2 1 (by decide) (by decide) (by norm_num [h])

theorem original_irreducible_six_centralizer_soluble
    {S V : Type} [Group S] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) S V) (hirr : Representation.IsIrreducible rho)
    (hd : Module.finrank (ZMod 2) V = 6) : IsSolvable (linearCentralizer rho) := by
  letI : Representation.IsIrreducible rho := hirr
  letI : Finite (linearCentralizer rho) :=
    Finite.of_injective (fun e : linearCentralizer rho => (e.val : V → V)) (by
      intro e f he
      apply Subtype.ext
      exact LinearEquiv.ext (congrFun he))
  have hV : Nat.card V = 64 := by
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2), Nat.card_zmod, hd]
    norm_num
  apply soluble_of_card_dvd_sixtyThree
  simpa only [hV] using centralizer_card_dvd_nonzero_card rho

end SymmetricSubgroupAsymptotics.CFSGIsotypicCentralizerOriginalSix
