import SymmetricSubgroupAsymptotics.NormalTargetShortTupleSource

/-! The complete epimorphism sum over adapted original generating tuples
and their target values. The arbitrary normal F and the literal projection
kernel are retained throughout. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.ProductProjectedEpimorphismCount
open MarkedC4

private theorem count_by_fibres {A B : Type} [Finite A] [Finite B]
    (f : A → B) (c : ℕ) (hf : ∀ b, Nat.card {a : A // f a = b} ≤ c) :
    Nat.card A ≤ Nat.card B * c := by
  letI : Fintype B := Fintype.ofFinite B
  calc
    Nat.card A = Nat.card (Σ b : B, {a : A // f a = b}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : B, Nat.card {a : A // f a = b} := Nat.card_sigma
    _ ≤ ∑ _b : B, c := Finset.sum_le_sum (fun b _ => hf b)
    _ = Nat.card B * c := by simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Fintype.card_eq_nat_card]; rfl

variable {G Q I : Type} [Group G] [Group Q] [Finite G] [Finite Q]
    [Fintype I] (P : I → Type) [∀ i, Group (P i)] [∀ i, Finite (P i)]
    (π : G →* ∀ i, P i)

local instance : Finite (G →* Q) :=
  Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

/-- Explicit ordinary target bound. The source can be any finite p-group
onto the displayed bounded product; there is no bounded-class assumption
on its original projection kernel. -/
theorem epimorphism_card_le
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G) (hQ : IsPGroup p Q)
    (hπ : Function.Surjective π) (F : Subgroup Q) [F.Normal]
    (M dN : ℕ) (hMpos : 0 < M) (hM : ∀ i, Nat.card (P i) ≤ M)
    (hd : ∀ U : Subgroup G, U.Normal →
      U ≤ commutator G ⊓ π.ker → normalGen U ≤ dN) :
    Nat.card {f : G →* Q // Function.Surjective f} ≤
      (genRank G + 1) ^ Nat.log p (Nat.card Q) *
        (Nat.card Q) ^ Nat.log p (Nat.card Q) *
        (Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q)) ^ dN *
        ((Nat.card Q) ^ ((M ^ Nat.log p (Nat.card Q) *
          Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q)) ^ Nat.card F) *
          (Nat.card (Subgroup.centralizer (F : Set Q))) ^ genRank G) := by
  obtain ⟨S, hS, hSgen, hSsupport⟩ :=
    PGroupProductAdaptedGenerators.exists_adapted_generators p P π hG hπ
  let q := Nat.log p (Nat.card Q)
  let T := Fin q → Option S
  let g : S → G := Subtype.val
  have hg : Subgroup.closure (Set.range g) = ⊤ := by
    simpa only [g, Subtype.range_coe_subtype, Finset.setOf_mem] using hSgen
  let v (t : T) : Fin q → G := fun a => (t a).elim 1 g
  let A (t : T) := {f : G →* Q // Subgroup.closure (Set.range (f ∘ v t)) = ⊤}
  let c := Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q)
  let bound := c ^ dN * ((Nat.card Q) ^ ((M ^ q * c) ^ Nat.card F) *
    (Nat.card (Subgroup.centralizer (F : Set Q))) ^ genRank G)
  have hv (t : T) (a : Fin q) :
      PGroupProductAdaptedGenerators.SingleSupport P π (v t a) := by
    cases ht : t a with
    | none => exact Or.inl (by simp only [v, ht, Option.elim_none, map_one])
    | some s => simpa only [v, ht, Option.elim_some] using hSsupport s s.property
  have hA (t : T) : Nat.card (A t) ≤ (Nat.card Q) ^ q * bound := by
    let V := Fin q → Q
    let values : A t → V := fun f => f.1 ∘ v t
    have hfibre (w : V) : Nat.card {f : A t // values f = w} ≤ bound := by
      let Y := {f : A t // values f = w}
      by_cases hY : Nonempty Y
      · obtain ⟨f₀⟩ := hY
        let j : Y → {f : G →* Q // ∀ a, f (v t a) = f₀.1.1 (v t a)} :=
          fun f => ⟨f.1.1, fun a => congrFun (f.2.trans f₀.2.symm) a⟩
        have hj : Function.Injective j := by
          intro f h he
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : {f : G →* Q //
            ∀ a, f (v t a) = f₀.1.1 (v t a)} => z.1) he
        have hb := NormalTargetShortTupleSource.prescribed_tuple_fibre_card_le P π
            p hG hQ (v t) (hv t) f₀.1.1 f₀.1.2 F M dN hMpos hM hd
        apply (Nat.card_le_card_of_injective j hj).trans
        simpa only [Fintype.card_fin, bound, c] using hb
      · letI : IsEmpty Y := not_nonempty_iff.mp hY
        simp only [Nat.card_of_isEmpty, zero_le]
    have hb := count_by_fibres values bound hfibre
    simpa only [V, Nat.card_fun, Nat.card_fin] using hb
  let E := {f : G →* Q // Function.Surjective f}
  have hcover (f : E) : ∃ t : T, Subgroup.closure (Set.range (f.1 ∘ v t)) = ⊤ :=
    exists_padded_generating_subtuple p hG g hg f.1 f.2
  let code : E → Σ t : T, A t := fun f =>
    ⟨(hcover f).choose, ⟨f.1, (hcover f).choose_spec⟩⟩
  have hcode : Function.Injective code := by
    intro f h he
    exact Subtype.ext (congrArg (fun z : Σ t : T, A t => z.2.1) he)
  have hT : Nat.card T ≤ (genRank G + 1) ^ q := by
    calc
      Nat.card T = (S.card + 1) ^ q := by
        change Nat.card (Fin q → Option S) = _
        rw [Nat.card_fun, Nat.card_fin, Finite.card_option]
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ _ := Nat.pow_le_pow_left (Nat.add_le_add_right hS 1) _
  letI : Fintype T := Fintype.ofFinite T
  calc
    Nat.card E ≤ Nat.card (Σ t : T, A t) := Nat.card_le_card_of_injective code hcode
    _ = ∑ t : T, Nat.card (A t) := Nat.card_sigma
    _ ≤ ∑ _t : T, (Nat.card Q) ^ q * bound :=
      Finset.sum_le_sum (fun t _ => hA t)
    _ = Nat.card T * ((Nat.card Q) ^ q * bound) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      rfl
    _ ≤ (genRank G + 1) ^ q * ((Nat.card Q) ^ q * bound) :=
      Nat.mul_le_mul_right _ hT
    _ = _ := by dsimp [bound, q, c]; ac_rfl

end SymmetricSubgroupAsymptotics.ProductProjectedEpimorphismCount
