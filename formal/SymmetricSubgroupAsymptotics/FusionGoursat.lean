import SymmetricSubgroupAsymptotics.JointSourceGraphs
import Mathlib.GroupTheory.Goursat

/-!
# Exact pointed-orbit Goursat data

The original quotient map is fixed. An actual subgroup on one distinguished
orbit and its complete complement is equivalent to its literal complement
image and one literal epimorphism. No quotient automorphism is divided out.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {U Q G : Type*} [Group U] [Group Q] [Group G]
variable {π : U →* Q}

/-- Actual subgroups with full original orbit action and its fixed axis. -/
abbrev FusionPointedSubgroups (π : U →* Q) (G : Type*) [Group G] :=
  {H : Subgroup (U × G) // H.map (MonoidHom.fst U G) = ⊤ ∧ H.goursatFst = π.ker}

/-- The complete complement image and one actual quotient map. -/
abbrev FusionGoursatData (G Q : Type*) [Group G] [Group Q] :=
  Σ J : Subgroup G, GroupEpimorphism J Q

/-- The literal quotient pullback inside the original product. -/
def fusionQuotientGraph (π : U →* Q) (J : Subgroup G) (β : J →* Q) :
    Subgroup (U × G) where
  carrier := {x | ∃ j : J, (j : G) = x.2 ∧ π x.1 = β j}
  one_mem' := ⟨1, rfl, by simp⟩
  mul_mem' := by
    rintro x y ⟨j,hj,hx⟩ ⟨k,hk,hy⟩
    refine ⟨j*k,by simp [hj,hk],?_⟩
    change π (x.1*y.1)=β (j*k)
    simp only [map_mul,hx,hy]
  inv_mem' := by
    rintro x ⟨j,hj,hx⟩
    refine ⟨j⁻¹,by simp [hj],?_⟩
    change π x.1⁻¹=β j⁻¹
    simp only [map_inv,hx]

@[simp] theorem fusionQuotientGraph_fibre (π : U →* Q) (J : Subgroup G)
    (β : J →* Q) (u : U) (j : J) :
    (u,(j:G)) ∈ fusionQuotientGraph π J β ↔ π u = β j := by
  constructor
  · rintro ⟨k,hk,h⟩
    have he : k=j := Subtype.ext hk
    simpa only [he] using h
  · exact fun h => ⟨j,rfl,h⟩

theorem fusionQuotientGraph_complement (π : U →* Q) (hπ : Function.Surjective π)
    (J : Subgroup G) (β : J →* Q) :
    (fusionQuotientGraph π J β).map (MonoidHom.snd U G) = J := by
  ext g
  constructor
  · rintro ⟨⟨u,g'⟩,⟨j,hj,h⟩,rfl⟩
    change g' ∈ J
    change (j:G)=g' at hj
    exact hj ▸ j.property
  · intro hg
    obtain ⟨u,hu⟩ := hπ (β ⟨g,hg⟩)
    exact ⟨(u,g),⟨⟨g,hg⟩,rfl,hu⟩,rfl⟩

theorem fusionQuotientGraph_full (π : U →* Q) (J : Subgroup G)
    (β : J →* Q) (hβ : Function.Surjective β) :
    (fusionQuotientGraph π J β).map (MonoidHom.fst U G) = ⊤ := by
  apply top_unique
  intro u _
  obtain ⟨j,hj⟩ := hβ (π u)
  exact ⟨(u,(j:G)),⟨j,rfl,hj.symm⟩,rfl⟩

@[simp] theorem fusionQuotientGraph_axis (π : U →* Q) (J : Subgroup G)
    (β : J →* Q) : (fusionQuotientGraph π J β).goursatFst = π.ker := by
  ext u
  rw [Subgroup.mem_goursatFst]
  change (u,((1:J):G)) ∈ fusionQuotientGraph π J β ↔ π u=1
  rw [fusionQuotientGraph_fibre,map_one]

def fusionGoursatEncode (π : U →* Q) : FusionGoursatData G Q → FusionPointedSubgroups π G :=
  fun d => ⟨fusionQuotientGraph π d.1 d.2.1,
    fusionQuotientGraph_full π d.1 d.2.1 d.2.2,fusionQuotientGraph_axis π d.1 d.2.1⟩

theorem fusionGoursatEncode_injective (π : U →* Q) (hπ : Function.Surjective π) :
    Function.Injective (fusionGoursatEncode (G := G) π) := by
  rintro ⟨J,β⟩ ⟨K,γ⟩ he
  have hH := congrArg Subtype.val he
  have hJ := congrArg (fun H : Subgroup (U×G) => H.map (MonoidHom.snd U G)) hH
  simp only [fusionGoursatEncode,fusionQuotientGraph_complement π hπ] at hJ
  subst K
  have hβ : β=γ := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro j
    obtain ⟨u,hu⟩ := hπ (β.1 j)
    have hm : (u,(j:G)) ∈ fusionQuotientGraph π J β.1 :=
      (fusionQuotientGraph_fibre π J β.1 u j).mpr hu
    change fusionQuotientGraph π J β.1 = fusionQuotientGraph π J γ.1 at hH
    rw [hH,fusionQuotientGraph_fibre] at hm
    exact hu.symm.trans hm
  subst γ
  rfl

/-- The original complement image, before any subsequent deletion. -/
def fusionActualComplement (H : FusionPointedSubgroups π G) : Subgroup G :=
  H.1.map (MonoidHom.snd U G)

def fusionComplementProjection (π : U →* Q) (H : FusionPointedSubgroups π G) :
    H.1 →* fusionActualComplement H :=
  ((MonoidHom.snd U G).comp H.1.subtype).codRestrict _
    (fun x => ⟨x.1,x.2,rfl⟩)

theorem fusionComplementProjection_surjective (π : U →* Q) (H : FusionPointedSubgroups π G) :
    Function.Surjective (fusionComplementProjection π H) := by
  rintro ⟨g,hg⟩
  obtain ⟨x,hx,he⟩ := hg
  exact ⟨⟨x,hx⟩,Subtype.ext he⟩

def fusionOriginalQuotient (π : U →* Q) (H : FusionPointedSubgroups π G) : H.1 →* Q :=
  π.comp ((MonoidHom.fst U G).comp H.1.subtype)

theorem fusionComplementProjection_kernel (π : U →* Q) (H : FusionPointedSubgroups π G) :
    (fusionComplementProjection π H).ker ≤ (fusionOriginalQuotient π H).ker := by
  intro x hx
  have hs : x.1.2=1 := congrArg Subtype.val hx
  have ha : x.1.1 ∈ H.1.goursatFst := by
    rw [Subgroup.mem_goursatFst]
    simpa only [← hs] using x.2
  rw [H.2.2] at ha
  exact ha

/-- The quotient map is descended from the actual H, with no splitting. -/
def fusionActualEpimorphism (π : U →* Q) (H : FusionPointedSubgroups π G) :
    fusionActualComplement H →* Q :=
  (fusionComplementProjection π H).liftOfSurjective
    (fusionComplementProjection_surjective π H)
    ⟨fusionOriginalQuotient π H,fusionComplementProjection_kernel π H⟩

@[simp] theorem fusionActualEpimorphism_apply (π : U →* Q)
    (H : FusionPointedSubgroups π G) (x : H.1) :
    fusionActualEpimorphism π H (fusionComplementProjection π H x) = π x.1.1 :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem fusionActualEpimorphism_surjective (π : U →* Q) (hπ : Function.Surjective π)
    (H : FusionPointedSubgroups π G) : Function.Surjective (fusionActualEpimorphism π H) := by
  intro q
  obtain ⟨u,hu⟩ := hπ q
  have hm : u ∈ H.1.map (MonoidHom.fst U G) := by rw [H.2.1]; trivial
  obtain ⟨x,hx,he⟩ := hm
  refine ⟨fusionComplementProjection π H ⟨x,hx⟩,?_⟩
  rw [fusionActualEpimorphism_apply]
  exact (congrArg π he).trans hu

theorem fusionActualEpimorphism_recovers (π : U →* Q) (H : FusionPointedSubgroups π G) :
    fusionQuotientGraph π (fusionActualComplement H) (fusionActualEpimorphism π H) = H.1 := by
  ext x
  constructor
  · rintro ⟨j,hj,hq⟩
    obtain ⟨y,hy⟩ := fusionComplementProjection_surjective π H j
    have hs : y.1.2=x.2 := (congrArg Subtype.val hy).trans hj
    have hq' : π x.1=π y.1.1 := by rw [← fusionActualEpimorphism_apply π H y,hy]; exact hq
    have ha : x.1*y.1.1⁻¹ ∈ H.1.goursatFst := by
      rw [H.2.2]
      change π (x.1*y.1.1⁻¹)=1
      simp [hq']
    have hm := H.1.mul_mem ((Subgroup.mem_goursatFst).mp ha) y.2
    have he : (x.1*y.1.1⁻¹,(1:G))*y.1=x := by ext <;> simp [hs]
    simpa only [he] using hm
  · intro hx
    exact ⟨fusionComplementProjection π H ⟨x,hx⟩,rfl,
      (fusionActualEpimorphism_apply π H ⟨x,hx⟩).symm⟩

theorem fusionGoursatEncode_surjective (π : U →* Q) (hπ : Function.Surjective π) :
    Function.Surjective (fusionGoursatEncode (G := G) π) := by
  intro H
  exact ⟨⟨fusionActualComplement H,fusionActualEpimorphism π H,
    fusionActualEpimorphism_surjective π hπ H⟩,
    Subtype.ext (fusionActualEpimorphism_recovers π H)⟩

/-- Exact actual-map classification, with no Aut(Q) divisor. -/
def fusionGoursatEquiv (π : U →* Q) (hπ : Function.Surjective π) :
    FusionPointedSubgroups π G ≃ FusionGoursatData G Q :=
  (Equiv.ofBijective (fusionGoursatEncode π)
    ⟨fusionGoursatEncode_injective π hπ,fusionGoursatEncode_surjective π hπ⟩).symm

/-- Every later survival predicate is retained on the actual original H. -/
def fusionGoursatRestrictedEquiv (π : U →* Q) (hπ : Function.Surjective π)
    (P : FusionPointedSubgroups π G → Prop) :
    {H : FusionPointedSubgroups π G // P H} ≃
      {d : FusionGoursatData G Q // P (fusionGoursatEncode π d)} :=
  (fusionGoursatEquiv π hπ).subtypeEquiv (fun H => by
    change P H ↔ P ((fusionGoursatEquiv π hπ).symm ((fusionGoursatEquiv π hπ) H))
    rw [Equiv.symm_apply_apply])

end SymmetricSubgroupAsymptotics
