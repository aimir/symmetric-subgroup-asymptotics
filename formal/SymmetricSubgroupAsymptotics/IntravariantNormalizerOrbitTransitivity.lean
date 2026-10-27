import SymmetricSubgroupAsymptotics.CFSGIntravariantFrattini
import Mathlib.GroupTheory.GroupAction.Transitive

/-! The elementary normalizer-transitivity contradiction used in the
minimal-transitive reduction. Every local orbit and embedding is actual. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.IntravariantNormalizerOrbitTransitivity
open CFSGReduction
variable {G X : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]

theorem normalizer_pretransitive (L : Subgroup G) [L.Normal]
    (H : Subgroup L) (hInv : Intravariant H)
    (hloc : ∀ (x : X) (l : L), ∃ k : L,
      k.val ∈ Subgroup.normalizer (H.map L.subtype : Set G) ∧
        k.val • x=l.val • x) :
    MulAction.IsPretransitive (Subgroup.normalizer (H.map L.subtype : Set G)) X := by
  let N := Subgroup.normalizer (H.map L.subtype : Set G)
  have hsup : N ⊔ L=⊤ := normalizer_map_subtype_sup_eq_top L H hInv
  constructor
  intro x y
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
  have hgs : g ∈ N ⊔ L := hsup.symm ▸ Subgroup.mem_top g
  obtain ⟨n,hn,l,hl,he⟩ := Subgroup.mem_sup_of_normal_right.mp hgs
  obtain ⟨k,hk,hkx⟩ := hloc x ⟨l,hl⟩
  refine ⟨⟨n*k.val,N.mul_mem hn hk⟩,?_⟩
  change (n*k.val) • x=y
  rw [mul_smul,hkx,←mul_smul,he]
  exact hg

/-- Minimal transitivity forces the displayed intravariant subgroup to
be normal in the original group, once its local normalizer fills L-orbits. -/
theorem mapped_subgroup_normal_of_minimal_transitive
    (hmin : ∀ N : Subgroup G, MulAction.IsPretransitive N X → N=⊤)
    (L : Subgroup G) [L.Normal] (H : Subgroup L) (hInv : Intravariant H)
    (hloc : ∀ (x : X) (l : L), ∃ k : L,
      k.val ∈ Subgroup.normalizer (H.map L.subtype : Set G) ∧
        k.val • x=l.val • x) : (H.map L.subtype).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  exact hmin _ (normalizer_pretransitive L H hInv hloc)

end SymmetricSubgroupAsymptotics.IntravariantNormalizerOrbitTransitivity
