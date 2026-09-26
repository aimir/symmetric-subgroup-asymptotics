import SymmetricSubgroupAsymptotics.BinaryStructuredTupleEpi
import SymmetricSubgroupAsymptotics.PrimeFrattiniGenerators
import Mathlib.Data.Finite.Card

/-! An unconditional structured epimorphism count for actual finite binary
groups. A basis of the original source Frattini quotient supplies actual
generators. Every onto map is covered by a fixed-length optional-index code
using those same generators, and each code has the proved center/derived
estimate. The source is not assumed to be a bounded-alphabet product.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

local instance structuredEpiHomFinite {G Q : Type*} [Group G] [Group Q]
    [Finite G] [Finite Q] : Finite (G →* Q) :=
  Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

/-- All literal epimorphisms obey the target-center and target-derived
slopes. The explicit remaining factor depends polynomially on the original
binary character rank, with degree and constant depending only on Q.
The raw subtype is definitionally the project's GroupEpimorphism type,
without importing its permutation-counting dependencies. -/
theorem binaryStructured_epimorphism_card_le
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (hG : IsPGroup 2 G) (hQ : IsPGroup 2 Q) :
    Nat.card {f : G →* Q // Function.Surjective f} ≤
      (binaryCharacterRank G + 1)^(Nat.log 2 (Nat.card Q)) *
        ((Nat.card (commutator Q))^(primeDerivedNormalRank 2 G) *
          ((Nat.card Q)^((Nat.card (commutator Q))^(Nat.log 2 (Nat.card Q))) *
            (Nat.card (Subgroup.center Q))^(binaryCharacterRank G))) := by
  obtain ⟨g,hg⟩ := exists_primeFrattini_generating_tuple 2 hG
  let q := Nat.log 2 (Nat.card Q)
  let T := Fin q → Option (Fin (binaryCharacterRank G))
  let x (t : T) (a : Fin q) : G := (t a).elim 1 g
  let E := {f : G →* Q // Function.Surjective f}
  let K (t : T) := {f : G →* Q // Subgroup.closure (Set.range (f ∘ x t)) = ⊤}
  let c := (Nat.card (commutator Q))^(primeDerivedNormalRank 2 G) *
    ((Nat.card Q)^((Nat.card (commutator Q))^q) *
      (Nat.card (Subgroup.center Q))^(binaryCharacterRank G))
  have hcover (f : E) : ∃ t : T, Subgroup.closure (Set.range (f.1 ∘ x t)) = ⊤ :=
    exists_padded_generating_subtuple 2 hG g hg f.1 f.2
  let j : E → Σ t : T, K t := fun f =>
    ⟨(hcover f).choose,⟨f.1,(hcover f).choose_spec⟩⟩
  have hj : Function.Injective j := by
    intro f g he
    apply Subtype.ext
    exact congrArg (fun t : Σ t : T, K t => t.2.1) he
  have hcode (t : T) : Nat.card (K t) ≤ c := by
    simpa only [K,c,Nat.card_fin] using
      binaryStructured_tuple_image_generating_card_le (x t) hG hQ
  have hT : Nat.card T = (binaryCharacterRank G + 1)^q := by
    change Nat.card (Fin q → Option (Fin (binaryCharacterRank G))) = _
    rw [Nat.card_fun,Nat.card_fin,Finite.card_option,Nat.card_fin]
  letI : Fintype T := Fintype.ofFinite T
  calc
    Nat.card E ≤ Nat.card (Σ t : T, K t) := Nat.card_le_card_of_injective j hj
    _ = ∑ t : T, Nat.card (K t) := Nat.card_sigma
    _ ≤ ∑ _t : T, c := Finset.sum_le_sum (fun t _ => hcode t)
    _ = Nat.card T * c := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      rfl
    _ = _ := by rw [hT]

end SymmetricSubgroupAsymptotics
