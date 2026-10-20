import SymmetricSubgroupAsymptotics.NormalTargetTupleFibre
import SymmetricSubgroupAsymptotics.NormalKernelProjectedIndex
import SymmetricSubgroupAsymptotics.NormalGeneratorCharacterBound
import SymmetricSubgroupAsymptotics.PGroupNormalSubgroupCount

/-! Joint incidence for an arbitrary normal target F, retaining the
literal source projection kernel. Only normal subgroups inside G' ∩ ker π
are charged. The top image of the chosen tuple commutator is paid once. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.NormalTargetProjectedIncidence
open MarkedC4

variable {G P Q : Type} [Group G] [Group P] [Group Q]
    [Finite G] [Finite Q]

local instance : Finite (G →* Q) :=
  Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

private theorem subgroup_card_mono {A B : Subgroup Q} (h : A ≤ B) :
    Nat.card A ≤ Nat.card B :=
  Nat.card_le_card_of_injective (Subgroup.inclusion h) (by
    intro a b he
    exact Subtype.ext (congrArg (fun z : B => (z : Q)) he))

/-- Uniform fixed-tuple incidence, before choosing a standardized short
tuple. No source nilpotency-class estimate or target-centrality premise
is used. -/
theorem fixed_tuple_card_le
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G) (hQ : IsPGroup p Q)
    (π : G →* P) {ι : Type} [Finite ι] (x : ι → G)
    (F : Subgroup Q) [F.Normal] (B dN : ℕ)
    (htop : Nat.card ((generatorNormalCommutator x).map π) ≤ B)
    (hd : ∀ U : Subgroup G, U.Normal →
      U ≤ commutator G ⊓ π.ker → normalGen U ≤ dN) :
    Nat.card {f : G →* Q // Function.Surjective f ∧
      Subgroup.closure (Set.range (f ∘ x)) = F} ≤
      (Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q)) ^ dN *
        ((Nat.card Q) ^ ((B * Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q)) ^
          Nat.card ι) *
          (Nat.card (Subgroup.centralizer (F : Set Q))) ^ genRank G) := by
  let D := generatorNormalCommutator x
  let E := D ⊓ π.ker
  let c := Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q)
  let A := {f : G →* Q // Function.Surjective f ∧
    Subgroup.closure (Set.range (f ∘ x)) = F}
  let T := NormalSubgroupsAtMostIndex E c
  have himage (f : A) : Nat.card (E.map f.1) ≤ c := by
    have hle := Subgroup.map_mono (show E ≤ D from inf_le_left) (f := f.1)
    rw [NormalTargetTupleFibre.normalCommutator_map x F f.1 f.2.1 f.2.2] at hle
    exact subgroup_card_mono hle
  have hindex (f : A) : (E ⊓ f.1.ker).relIndex E ≤ c := by
    rw [Subgroup.inf_relIndex_left, E.relIndex_ker]
    exact himage f
  let code : A → T := fun f =>
    ⟨E ⊓ f.1.ker, inferInstance, inf_le_left, hindex f⟩
  have hcount : Nat.card T ≤ c ^ dN := by
    obtain ⟨a, ha⟩ := (hQ.to_subgroup (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q)).exists_card_eq
    change Nat.card (NormalSubgroupsAtMostIndex E c) ≤ c ^ dN
    dsimp [c]
    rw [ha, ← pow_mul]
    apply pGroup_normal_subgroup_count_le hG E dN
    intro U hU hUE
    letI : U.Normal := hU
    exact (primeRelativeHead_le_normalGen p U).trans (hd U hU
      (le_inf (hUE.trans inf_le_left |>.trans (generatorNormalCommutator_le_derived x))
        (hUE.trans inf_le_right)))
  have hfibre (H : T) : Nat.card {f : A // code f = H} ≤
      (Nat.card Q) ^ ((B * c) ^ Nat.card ι) *
        (Nat.card (Subgroup.centralizer (F : Set Q))) ^ genRank G := by
    let Y := {f : A // code f = H}
    by_cases hY : Nonempty Y
    · obtain ⟨f₀⟩ := hY
      letI : H.1.Normal := H.2.1
      have hH : E ⊓ f₀.1.1.ker = H.1 :=
        congrArg (fun z : T => z.1) f₀.2
      have hquot : Nat.card (D.map (QuotientGroup.mk' H.1)) ≤ B * c := by
        have hrel : (E ⊓ f₀.1.1.ker).relIndex D =
            Nat.card (D.map π) * Nat.card (E.map f₀.1.1) := by
          rw [← NormalKernelProjectedIndex.quotient_card_eq D π f₀.1.1]
          simpa only [QuotientGroup.ker_mk'] using
            D.relIndex_ker (QuotientGroup.mk' (E ⊓ f₀.1.1.ker))
        calc
          _ = H.1.relIndex D := by
            simpa only [QuotientGroup.ker_mk'] using
              (D.relIndex_ker (QuotientGroup.mk' H.1)).symm
          _ = (E ⊓ f₀.1.1.ker).relIndex D := congrArg (fun U => U.relIndex D) hH.symm
          _ = _ := hrel
          _ ≤ _ := Nat.mul_le_mul htop (himage f₀.1)
      let j : Y → {f : G →* Q // H.1 ≤ f.ker ∧
          Subgroup.closure (Set.range (f ∘ x)) = F} := fun f =>
        ⟨f.1.1, (congrArg (fun z : T => z.1) f.2).symm.le.trans inf_le_right,
          f.1.2.2⟩
      have hj : Function.Injective j := by
        intro f g he
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun z : {f : G →* Q // H.1 ≤ f.ker ∧
            Subgroup.closure (Set.range (f ∘ x)) = F} => z.1) he
      exact (Nat.card_le_card_of_injective j hj).trans
        ((NormalTargetTupleFibre.selected_card_le x H.1 F).trans
          (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.card_pos : 0 < Nat.card Q)
            (Nat.pow_le_pow_left hquot _))))
    · letI : IsEmpty Y := not_nonempty_iff.mp hY
      simp only [Nat.card_of_isEmpty, zero_le]
  letI : Fintype T := Fintype.ofFinite T
  calc
    Nat.card A = Nat.card (Σ H : T, {f : A // code f = H}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv code)).symm
    _ = ∑ H : T, Nat.card {f : A // code f = H} := Nat.card_sigma
    _ ≤ ∑ _H : T, ((Nat.card Q) ^ ((B * c) ^ Nat.card ι) *
        (Nat.card (Subgroup.centralizer (F : Set Q))) ^ genRank G) :=
      Finset.sum_le_sum (fun H _ => hfibre H)
    _ = Nat.card T * _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      rfl
    _ ≤ _ := Nat.mul_le_mul_right _ hcount

end SymmetricSubgroupAsymptotics.NormalTargetProjectedIncidence
