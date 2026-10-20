import SymmetricSubgroupAsymptotics.NormalTargetProjectedIncidence
import SymmetricSubgroupAsymptotics.ProductCoordinateSupport

/-! A short original tuple whose image generates the target supplies a
fixed tuple over every normal target subgroup. Its original top support
is retained, and all maps in the prescribed tuple-value fibre are counted
together through their actual projection kernels. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.NormalTargetShortTupleSource
open MarkedC4

variable {G Q I : Type} [Group G] [Group Q] [Finite G] [Finite Q]
    [Fintype I] (P : I → Type) [∀ i, Group (P i)] [∀ i, Finite (P i)]
    (π : G →* ∀ i, P i)

local instance : Finite (G →* Q) :=
  Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

theorem prescribed_tuple_fibre_card_le
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G) (hQ : IsPGroup p Q)
    {J : Type} [Fintype J] (v : J → G)
    (hv : ∀ j, PGroupProductAdaptedGenerators.SingleSupport P π (v j))
    (f₀ : G →* Q) (hgen : Subgroup.closure (Set.range (f₀ ∘ v)) = ⊤)
    (F : Subgroup Q) [F.Normal] (M dN : ℕ) (hMpos : 0 < M)
    (hM : ∀ i, Nat.card (P i) ≤ M)
    (hd : ∀ U : Subgroup G, U.Normal →
      U ≤ commutator G ⊓ π.ker → normalGen U ≤ dN) :
    Nat.card {f : G →* Q // ∀ j, f (v j) = f₀ (v j)} ≤
      (Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q)) ^ dN *
        ((Nat.card Q) ^ ((M ^ Fintype.card J *
          Nat.card (⁅F, (⊤ : Subgroup Q)⁆ : Subgroup Q)) ^ Nat.card F) *
          (Nat.card (Subgroup.centralizer (F : Set Q))) ^ genRank G) := by
  let V := Subgroup.closure (Set.range v)
  have hV : Function.Surjective (f₀.comp V.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, V.range_subtype]
    dsimp [V]
    rw [MonoidHom.map_closure]
    simpa only [Set.range_comp] using hgen
  choose x hx using fun a : F => hV a.1
  let u : F → G := fun a => (x a : G)
  have hu (a : F) : u a ∈ V := (x a).property
  have hux (a : F) : f₀ (u a) = a.1 := hx a
  obtain ⟨T, hT, hvT⟩ := ProductCoordinateSupport.exists_tuple_support P π v hv
  have huTop : (generatorNormalCommutator u).map π ≤
      ProductCoordinateSupport.box P T :=
    ProductCoordinateSupport.normalCommutator_top_le P π v u T hvT hu
  have htop : Nat.card ((generatorNormalCommutator u).map π) ≤ M ^ Fintype.card J := by
    have hm : Nat.card ((generatorNormalCommutator u).map π) ≤
        Nat.card (ProductCoordinateSupport.box P T) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion huTop) (by
        intro a b he
        exact Subtype.ext (congrArg
          (fun z : ProductCoordinateSupport.box P T => (z : ∀ i, P i)) he))
    exact hm.trans ((ProductCoordinateSupport.card_box_le P T M hM).trans
      (Nat.pow_le_pow_right hMpos hT))
  let A := {f : G →* Q // ∀ j, f (v j) = f₀ (v j)}
  have hsame (f : A) : Set.EqOn f.1 f₀ (V : Set G) := by
    apply MonoidHom.eqOn_closure
    rintro _ ⟨j, rfl⟩
    exact f.2 j
  have honto (f : A) : Function.Surjective f.1 := by
    apply tuple_image_generating_surjective v f.1
    have he : f.1 ∘ v = f₀ ∘ v := funext f.2
    rwa [he]
  have huf (f : A) : Subgroup.closure (Set.range (f.1 ∘ u)) = F := by
    have hrange : Set.range (f.1 ∘ u) = (F : Set Q) := by
      ext a
      constructor
      · rintro ⟨z, rfl⟩
        change f.1 (u z) ∈ F
        rw [hsame f (hu z), hux]
        exact z.property
      · intro ha
        refine ⟨⟨a, ha⟩, ?_⟩
        exact (hsame f (hu ⟨a, ha⟩)).trans (hux ⟨a, ha⟩)
    rw [hrange, Subgroup.closure_eq]
  let j : A → {f : G →* Q // Function.Surjective f ∧
      Subgroup.closure (Set.range (f ∘ u)) = F} := fun f => ⟨f.1, honto f, huf f⟩
  have hj : Function.Injective j := by
    intro f g he
    exact Subtype.ext (congrArg
      (fun z : {f : G →* Q // Function.Surjective f ∧
        Subgroup.closure (Set.range (f ∘ u)) = F} => z.1) he)
  exact (Nat.card_le_card_of_injective j hj).trans
    (NormalTargetProjectedIncidence.fixed_tuple_card_le p hG hQ π u F
      (M ^ Fintype.card J) dN htop hd)

end SymmetricSubgroupAsymptotics.NormalTargetShortTupleSource
