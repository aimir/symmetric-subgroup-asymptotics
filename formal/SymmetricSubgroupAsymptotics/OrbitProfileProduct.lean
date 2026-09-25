import SymmetricSubgroupAsymptotics.OrbitProfileAssembly

/-!
# Literal products and full profile subgroups

The direct product of the original local action groups acts independently on
the original blocks. Actual subgroup map/comap along this faithful action
identifies full product subgroups with the literal full model fibre.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {ι : Type*} {Ω : ι → Type*}

/-- The group of independent original actions on all occurrences. -/
abbrev OrbitProfileProductGroup (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) := ∀ i, Fin (m i) → U i

/-- The literal permutation acting independently within each original block. -/
def orbitProfileProductPermutation {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))} (d : OrbitProfileProductGroup m U) :
    Equiv.Perm (OrbitProfilePoints Ω m) where
  toFun z := ⟨z.1, z.2.1, (d z.1 z.2.1 : Equiv.Perm (Ω z.1)) z.2.2⟩
  invFun z := ⟨z.1, z.2.1, (d z.1 z.2.1 : Equiv.Perm (Ω z.1)).symm z.2.2⟩
  left_inv z := by rcases z with ⟨i,j,x⟩; simp
  right_inv z := by rcases z with ⟨i,j,x⟩; simp

/-- The product action is an actual permutation-valued group homomorphism. -/
def orbitProfileProductAction (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    OrbitProfileProductGroup m U →* Equiv.Perm (OrbitProfilePoints Ω m) where
  toFun := orbitProfileProductPermutation
  map_one' := by apply Equiv.ext; rintro ⟨i,j,x⟩; rfl
  map_mul' _ _ := by apply Equiv.ext; rintro ⟨i,j,x⟩; rfl

/-- No coordinates or local group elements are lost by the product action. -/
theorem orbitProfileProductAction_injective (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    Function.Injective (orbitProfileProductAction m U) := by
  intro a b h
  funext i j
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have he := Equiv.congr_fun h ⟨i,j,x⟩
  change (⟨i,j,(a i j : Equiv.Perm (Ω i)) x⟩ : OrbitProfilePoints Ω m) =
    ⟨i,j,(b i j : Equiv.Perm (Ω i)) x⟩ at he
  have hp : (j,(a i j : Equiv.Perm (Ω i)) x) = (j,(b i j : Equiv.Perm (Ω i)) x) := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
  exact congrArg Prod.snd hp

/-- Actual coordinate-surjectivity of a subgroup of the product group. -/
def OrbitProfileProductFull (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
    (H : Subgroup (OrbitProfileProductGroup m U)) : Prop :=
  ∀ i (j : Fin (m i)) (u : U i), ∃ h : H, h.1 i j = u

/-- Evaluation at one literal occurrence. -/
def orbitProfileProductProjection (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) (i : ι) (j : Fin (m i)) :
    OrbitProfileProductGroup m U →* U i where
  toFun d := d i j
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The coordinate-surjectivity predicate is exactly full subgroup image
under each original evaluation homomorphism. -/
theorem orbitProfileProductFull_iff_map_eq_top (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
    (H : Subgroup (OrbitProfileProductGroup m U)) :
    OrbitProfileProductFull m U H ↔
      ∀ i (j : Fin (m i)), H.map (orbitProfileProductProjection m U i j) = ⊤ := by
  constructor
  · intro h i j
    apply top_unique
    intro u _
    obtain ⟨d,hd⟩ := h i j u
    exact Subgroup.mem_map.mpr ⟨d.1,d.2,hd⟩
  · intro h i j u
    have hu : u ∈ H.map (orbitProfileProductProjection m U i j) := by rw [h i j]; trivial
    obtain ⟨d,hd,he⟩ := Subgroup.mem_map.mp hu
    exact ⟨⟨d,hd⟩,he⟩

/-- Mapping a full product subgroup gives its literal full permutation
subgroup, preserving every original coordinate projection. -/
theorem orbitProfileProductFull_map {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {H : Subgroup (OrbitProfileProductGroup m U)} (hH : OrbitProfileProductFull m U H) :
    OrbitProfileFull U 1 (H.map (orbitProfileProductAction m U)) := by
  constructor
  · intro h i j
    obtain ⟨d,hd,he⟩ := Subgroup.mem_map.mp h.2
    refine ⟨d i j,fun x => ?_⟩
    change h.1 ⟨i,j,x⟩ = ⟨i,j,(d i j : Equiv.Perm (Ω i)) x⟩
    rw [← he]
    rfl
  · intro i j u
    obtain ⟨d,hd⟩ := hH i j u
    refine ⟨⟨orbitProfileProductAction m U d.1,Subgroup.mem_map.mpr ⟨d.1,d.2,rfl⟩⟩,
      fun x => ?_⟩
    change (⟨i,j,(d.1 i j : Equiv.Perm (Ω i)) x⟩ : OrbitProfilePoints Ω m) = ⟨i,j,u.1 x⟩
    rw [hd]

/-- The maps condition alone forces every actual subgroup element into the
literal product-action range; no block-product hypothesis is assumed. -/
theorem orbitProfileFull_le_product_range {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {K : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))} (hK : OrbitProfileFull U 1 K) :
    K ≤ (orbitProfileProductAction m U).range := by
  intro h hh
  choose d hd using (fun i j => hK.maps ⟨h,hh⟩ i j)
  refine ⟨d,?_⟩
  apply Equiv.ext
  rintro ⟨i,j,x⟩
  exact (hd i j x).symm

/-- Comapping a literal full permutation subgroup recovers a full subgroup
of the original independent action product. -/
theorem orbitProfileFull_comap {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {K : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))} (hK : OrbitProfileFull U 1 K) :
    OrbitProfileProductFull m U (K.comap (orbitProfileProductAction m U)) := by
  intro i j u
  obtain ⟨h,hh⟩ := hK.full i j u
  obtain ⟨d,hd⟩ := orbitProfileFull_le_product_range hK h.2
  refine ⟨⟨d,?_⟩,?_⟩
  · change orbitProfileProductAction m U d ∈ K
    rw [hd]
    exact h.2
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    have he := hh x
    change h.1 ⟨i,j,x⟩ = ⟨i,j,u.1 x⟩ at he
    rw [← hd] at he
    change (⟨i,j,(d i j : Equiv.Perm (Ω i)) x⟩ : OrbitProfilePoints Ω m) =
      ⟨i,j,u.1 x⟩ at he
    have hp : (j,(d i j : Equiv.Perm (Ω i)) x) = (j,u.1 x) := by
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
    exact congrArg Prod.snd hp

/-- Map and comap along the faithful action identify the full original
product subgroups with the literal model fibre used in profile assembly. -/
def orbitProfileProductFullEquiv (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    {H : Subgroup (OrbitProfileProductGroup m U) // OrbitProfileProductFull m U H} ≃
      {K : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) // OrbitProfileFull U 1 K} where
  toFun H := ⟨H.1.map (orbitProfileProductAction m U),orbitProfileProductFull_map H.2⟩
  invFun K := ⟨K.1.comap (orbitProfileProductAction m U),orbitProfileFull_comap K.2⟩
  left_inv H := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective (orbitProfileProductAction_injective m U) H.1
  right_inv K := by
    apply Subtype.ext
    exact Subgroup.map_comap_eq_self (orbitProfileFull_le_product_range K.2)

/-- Exact cardinal bridge; neither family is defined by a desired count. -/
theorem orbitProfileProductFull_card (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    Nat.card {H : Subgroup (OrbitProfileProductGroup m U) // OrbitProfileProductFull m U H} =
      Nat.card {K : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) // OrbitProfileFull U 1 K} :=
  Nat.card_congr (orbitProfileProductFullEquiv m U)

end SymmetricSubgroupAsymptotics
