import SymmetricSubgroupAsymptotics.CoinducedLeadingCoordinates
import SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight

/-! Full vector-valued leading rows in the original coinduced module.
Raising preserves the full fibre coefficient, while an actual core element
performs any specified original local coefficient action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CoinducedLeadingRows
open FiniteRowLeadingWeight

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {n : ℕ}

def rows (H : Subgroup G) (rho : Representation k H V) (T : Fin n → G) :
    Representation.coindV H.subtype rho →ₗ[k] (Fin n → V) where
  toFun f a := f.1 (T a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Raise one original leading row to a comparable row, with no change
in its full local vector coefficient. -/
theorem raise_leading
    (H : Subgroup G) (rho : Representation k H V) (T : Fin n → G)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin n, x=h*T a)
    (rel : Fin n → Fin n → Prop)
    (hunique : ∀ a b, T a*(T b)⁻¹∈H → a=b)
    (htri : CosetTriangular H T (· < ·) rel)
    (f : Representation.coindV H.subtype rho) (a b : Fin n)
    (hf : HasLeading (rows H rho T f) a) (hab : rel a b) :
    HasLeading (rows H rho T
      ((Representation.coind H.subtype rho) (CoinducedLeadingCoordinates.raisingElement T a b) f)) b ∧
    rows H rho T ((Representation.coind H.subtype rho)
      (CoinducedLeadingCoordinates.raisingElement T a b) f) b=rows H rho T f a := by
  have htarget : rows H rho T ((Representation.coind H.subtype rho)
      (CoinducedLeadingCoordinates.raisingElement T a b) f) b=rows H rho T f a :=
    CoinducedLeadingCoordinates.target_row H rho T a b f
  refine ⟨⟨by rw [htarget]; exact hf.1,?_⟩,htarget⟩
  intro c hbc
  obtain ⟨h,hh,d,hd⟩ := hfactor (T c*CoinducedLeadingCoordinates.raisingElement T a b)
  have had := CoinducedLeadingCoordinates.source_row_gt H T rel hunique htri
    hab hbc h hh hd
  change f.1 (T c*CoinducedLeadingCoordinates.raisingElement T a b)=0
  rw [hd]
  change f.1 (H.subtype ⟨h,hh⟩*T d)=0
  have hfd : f.1 (T d)=0 := hf.2 d had
  rw [f.2 ⟨h,hh⟩ (T d),hfd,map_zero]

/-- Any original core element acts locally on each row, through its
actual conjugate in H. In particular zero rows stay zero. -/
theorem core_translation_row
    (H : Subgroup G) (rho : Representation k H V) (T : Fin n → G)
    (f : Representation.coindV H.subtype rho) (g : G) (hg : g∈H.normalCore) (a : Fin n) :
    ∃ h : H, rows H rho T ((Representation.coind H.subtype rho) g f) a=
      rho h (rows H rho T f a) := by
  have hh : T a*g*(T a)⁻¹∈H := H.normalCore_le
    ((inferInstance : H.normalCore.Normal).conj_mem g hg (T a))
  refine ⟨⟨T a*g*(T a)⁻¹,hh⟩,?_⟩
  change f.1 (T a*g)=rho ⟨T a*g*(T a)⁻¹,hh⟩ (f.1 (T a))
  have he : T a*g=(T a*g*(T a)⁻¹)*T a := by group
  exact (congrArg f.1 he).trans (f.2 ⟨T a*g*(T a)⁻¹,hh⟩ (T a))

/-- An actual local subgroup inside the original core can change the
leading coefficient by its displayed local action, without moving its row. -/
theorem twist_leading
    (H : Subgroup G) (rho : Representation k H V) (T : Fin n → G)
    (L : Subgroup H) (hL : L.map H.subtype≤H.normalCore)
    (f : Representation.coindV H.subtype rho) (a : Fin n)
    (hf : HasLeading (rows H rho T f) a) (l : L)
    (hne : rho (l : H) (rows H rho T f a)≠0) :
    ∃ g : G, HasLeading (rows H rho T ((Representation.coind H.subtype rho) g f)) a ∧
      rows H rho T ((Representation.coind H.subtype rho) g f) a=
        rho (l : H) (rows H rho T f a) := by
  let g : G := (T a)⁻¹*((l : H) : G)*T a
  have hl : ((l : H) : G)∈H.normalCore := hL ⟨l,l.property,rfl⟩
  have hg : g∈H.normalCore := by
    simpa only [g,inv_inv] using
      (inferInstance : H.normalCore.Normal).conj_mem _ hl (T a)⁻¹
  have htarget : rows H rho T ((Representation.coind H.subtype rho) g f) a=
      rho (l : H) (rows H rho T f a) := by
    change f.1 (T a*g)=rho (l : H) (f.1 (T a))
    have he : T a*g=((l : H) : G)*T a := by dsimp [g]; group
    rw [he]
    exact f.2 (l : H) (T a)
  refine ⟨g,⟨by rw [htarget]; exact hne,?_⟩,htarget⟩
  intro b hab
  obtain ⟨h,hh⟩ := core_translation_row H rho T f g hg b
  rw [hh,hf.2 b hab,map_zero]

end SymmetricSubgroupAsymptotics.CoinducedLeadingRows
