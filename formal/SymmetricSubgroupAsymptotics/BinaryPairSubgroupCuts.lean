import SymmetricSubgroupAsymptotics.BinaryPairFixedCounts

/-! Construct central cuts from literal subgroups of the original kernel.
Generator commutators certify centrality; fixed-preimage cardinalities
then compute the capacity of this same quotient section. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {p : ℕ} {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod p) V]

def sectionSubgroupImage (q : K →* Multiplicative V) (L : Subgroup K) :
    Submodule (ZMod p) V :=
  ((AddMonoidHom.toMultiplicativeRight.symm q).comp L.subtype.toAdditive).range.toZModSubmodule p

theorem sectionSubgroupImage_mem_iff (q : K →* Multiplicative V) (L : Subgroup K)
    (hL : q.ker≤L) (k : K) : (q k).toAdd∈sectionSubgroupImage (p := p) q L ↔ k∈L := by
  constructor
  · rintro ⟨l,hl⟩
    have he : q (l.toMul:K)=q k := congrArg Multiplicative.ofAdd hl
    have hk : k⁻¹*(l.toMul:K)∈L := hL ((MonoidHom.eq_iff q).mp he)
    have hkm : k⁻¹∈L := by
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using L.mul_mem hk (L.inv_mem l.toMul.2)
    simpa only [inv_inv] using L.inv_mem hkm
  · intro hk
    exact ⟨Additive.ofMul (⟨k,hk⟩:L),rfl⟩

def sectionSubgroupCutMap (q : K →* Multiplicative V) (L : Subgroup K) :
    K →* Multiplicative (V ⧸ sectionSubgroupImage (p := p) q L) :=
  (sectionSubgroupImage (p := p) q L).mkQ.toAddMonoidHom.toMultiplicative.comp q

theorem sectionSubgroupCutMap_surjective (q : K →* Multiplicative V)
    (hq : Function.Surjective q) (L : Subgroup K) :
    Function.Surjective (sectionSubgroupCutMap (p := p) q L) := by
  intro v
  obtain ⟨x,hx⟩ := (sectionSubgroupImage (p := p) q L).mkQ_surjective v.toAdd
  obtain ⟨k,hk⟩ := hq (Multiplicative.ofAdd x)
  refine ⟨k,?_⟩
  change Multiplicative.ofAdd ((sectionSubgroupImage (p := p) q L).mkQ (q k).toAdd)=v
  rw [hk]
  exact congrArg Multiplicative.ofAdd hx

theorem sectionSubgroupCutMap_ker (q : K →* Multiplicative V) (L : Subgroup K)
    (hL : q.ker≤L) : (sectionSubgroupCutMap (p := p) q L).ker=L := by
  ext k
  change (sectionSubgroupImage (p := p) q L).mkQ (q k).toAdd=0 ↔ k∈L
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact sectionSubgroupImage_mem_iff (p := p) q L hL k

section BinaryGenerators
variable {G K₀ V₀ ι : Type} [Group G] [Group K₀]
    [AddCommGroup V₀] [Module (ZMod 2) V₀]

/-- Only commutators with original generators are checked. Their exact
vanishing in the original section proves that the selected cut is central. -/
theorem sectionSubgroupImage_le_invariants_of_generators
    (q : K₀ →* Multiplicative V₀) (ρ : Representation (ZMod 2) G V₀)
    (α : G →* MulAut K₀)
    (heq : ∀ g k, ρ g (q k).toAdd=(q (α g k)).toAdd)
    (generators : ι→G) (hgen : Subgroup.closure (Set.range generators)=⊤)
    (L : Subgroup K₀)
    (hcomm : ∀ j, ∀ k : L, (k:K₀)⁻¹*α (generators j) (k:K₀)∈q.ker) :
    sectionSubgroupImage (p := 2) q L≤ρ.invariants := by
  rintro v ⟨k,rfl⟩
  apply (binaryPair_invariants_iff_generators ρ generators hgen _).mpr
  intro j
  change ρ (generators j) (q (k.toMul:K₀)).toAdd=(q (k.toMul:K₀)).toAdd
  rw [heq]
  exact congrArg Multiplicative.toAdd ((MonoidHom.eq_iff q).mpr (hcomm j k.toMul))

/-- A complete fixed-preimage test uses the same original generators. -/
theorem sectionFixedPreimage_mem_iff_generators
    (q : K₀ →* Multiplicative V₀) (ρ : Representation (ZMod 2) G V₀)
    (α : G →* MulAut K₀)
    (heq : ∀ g k, ρ g (q k).toAdd=(q (α g k)).toAdd)
    (generators : ι→G) (hgen : Subgroup.closure (Set.range generators)=⊤) (k : K₀) :
    k∈sectionSubspacePreimage q ρ.invariants ↔
      ∀ j, k⁻¹*α (generators j) k∈q.ker := by
  change (q k).toAdd∈ρ.invariants ↔ _
  rw [binaryPair_invariants_iff_generators ρ generators hgen]
  constructor
  · intro h j
    apply (MonoidHom.eq_iff q).mp
    apply Multiplicative.toAdd.injective
    exact (heq _ k).symm.trans (h j)
  · intro h j
    rw [heq]
    exact congrArg Multiplicative.toAdd ((MonoidHom.eq_iff q).mpr (h j))

end BinaryGenerators
end SymmetricSubgroupAsymptotics
