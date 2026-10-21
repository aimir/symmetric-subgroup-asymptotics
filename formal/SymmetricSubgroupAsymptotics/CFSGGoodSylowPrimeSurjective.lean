import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime
import SymmetricSubgroupAsymptotics.SylowActualNormalizerLift

/-! Good Sylow data descends through the actual surjective homomorphism.
Normalizer surjectivity is the proved Frattini lifting theorem for the
same Sylow subgroup, and requires no coprime-kernel or splitting premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem two_conjugates_generate_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (P : Subgroup G) (g : G)
    (hgen : Subgroup.closure ((P : Set G) ∪
      P.map (MulAut.conj g).toMonoidHom) = ⊤) :
    Subgroup.closure (((P.map f) : Set H) ∪
      (P.map f).map (MulAut.conj (f g)).toMonoidHom) = ⊤ := by
  let K := Subgroup.closure (((P.map f) : Set H) ∪
    (P.map f).map (MulAut.conj (f g)).toMonoidHom)
  have hP : P ≤ K.comap f := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl ⟨x,hx,rfl⟩)
  have hC : P.map (MulAut.conj g).toMonoidHom ≤ K.comap f := by
    rintro _ ⟨x,hx,rfl⟩
    change f (g*x*g⁻¹) ∈ K
    rw [map_mul,map_mul,map_inv]
    exact Subgroup.subset_closure (Or.inr ⟨f x,⟨x,hx,rfl⟩,rfl⟩)
  have hle := (Subgroup.closure_le (K.comap f)).mpr (Set.union_subset hP hC)
  rw [hgen] at hle
  apply top_unique
  intro y _
  obtain ⟨x,rfl⟩ := hf y
  exact hle (Subgroup.mem_top x)

/-- The original soluble normalizer maps onto the normalizer of its
actual Sylow image. -/
theorem goodSylowPrime_surjective {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) {p : ℕ}
    (hp : GoodSylowPrime G p) : GoodSylowPrime H p := by
  obtain ⟨hprime,P,g,hsol,hgen⟩ := hp
  letI goodSylowPrimeSurjectivePrime : Fact p.Prime := ⟨hprime⟩
  let Q : Sylow p H := P.mapSurjective (f := f) hf
  refine ⟨hprime,Q,f g,?_,?_⟩
  · let N := Subgroup.normalizer (P : Set G)
    let M := Subgroup.normalizer (((P : Subgroup G).map f) : Set H)
    letI goodSylowPrimeSurjectiveNormalizer : IsSolvable N := hsol
    let fn : N →* M :=
      { toFun := fun x => ⟨f x.val,
          (P : Subgroup G).le_normalizer_map f ⟨x.val,x.property,rfl⟩⟩
        map_one' := Subtype.ext f.map_one
        map_mul' := fun x y => Subtype.ext (f.map_mul x.val y.val) }
    have hfn : Function.Surjective fn := by
      intro y
      obtain ⟨x,hx,hxy⟩ := SylowActualNormalizerLift.exists_lift f hf P y.val y.property
      exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
    exact solvable_of_surjective (f := fn) hfn
  · exact two_conjugates_generate_surjective f hf (P : Subgroup G) g hgen

end SymmetricSubgroupAsymptotics.CFSGReduction
