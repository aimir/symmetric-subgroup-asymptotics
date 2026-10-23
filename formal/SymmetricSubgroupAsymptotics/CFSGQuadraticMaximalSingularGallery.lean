import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane
import Mathlib.Order.Minimal
import Mathlib.Logic.Relation

/-! Inclusion-maximal Q-singular spaces have a connected gallery whose
steps lose at most one intersection dimension. The proof uses actual
Q-singularity throughout and requires no split dimension identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalSingularGallery
open CFSGOrthogonalDIndexQuadraticCorrection CFSGOrthogonalDIndexQuadraticNeighborPlane
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

def MaximalSingular (Q : QuadraticForm K V) (S : Submodule K V) : Prop :=
  (∀ x ∈ S, Q x = 0) ∧ ∀ T : Submodule K V, (∀ x ∈ T, Q x = 0) → S ≤ T → T = S

theorem exists_maximal_ge (Q : QuadraticForm K V) (S : Submodule K V)
    (hS : ∀ x ∈ S, Q x = 0) : ∃ M, S ≤ M ∧ MaximalSingular Q M := by
  obtain ⟨M, hSM, hM⟩ := exists_maximal_ge_of_wellFoundedGT
    (fun T : Submodule K V => ∀ x ∈ T, Q x = 0) S hS
  exact ⟨M, hSM, hM.1, fun T hT hMT => (hM.2 hT hMT).antisymm hMT⟩

theorem finrank_inf_ker_add_one_ge (S : Submodule K V) (phi : V →ₗ[K] K) :
    Module.finrank K S ≤ Module.finrank K (S ⊓ phi.ker : Submodule K V) + 1 := by
  let f : S →ₗ[K] K := phi.comp S.subtype
  have hr : Module.finrank K f.range ≤ 1 := by
    simpa using (Submodule.finrank_le (R := K) f.range)
  have hn := LinearMap.finrank_range_add_finrank_ker (K := K) (V := S) (V₂ := K) f
  have he : f.ker.map S.subtype = S ⊓ phi.ker := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.property, hv⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hd : Module.finrank K f.ker = Module.finrank K (S ⊓ phi.ker : Submodule K V) := by
    rw [← he]
    exact (Submodule.equivMapOfInjective S.subtype S.subtype_injective f.ker).finrank_eq
  omega

theorem maximal_exchange_towards (Q : QuadraticForm K V) (S T : Submodule K V)
    (hS : MaximalSingular Q S) (hT : MaximalSingular Q T) (y : V) (hyT : y ∈ T) (hyS : y ∉ S) :
    ∃ M, MaximalSingular Q M ∧
      Module.finrank K S ≤ Module.finrank K (S ⊓ M : Submodule K V) + 1 ∧ S ⊓ T < M ⊓ T := by
  let phi := Q.polarBilin y
  let C := S ⊓ phi.ker
  have hCS : C ≤ S := inf_le_left
  have hyC (x : V) (hx : x ∈ C) : Q.polarBilin y x = 0 := hx.2
  have hCy (x : V) (hx : x ∈ C) : Q.polarBilin x y = 0 :=
    (QuadraticMap.polar_comm (Q : V → K) x y).trans (hyC x hx)
  have hC : ∀ x ∈ C, Q x = 0 := fun x hx => hS.1 x (hCS hx)
  have hy : Q y = 0 := hT.1 y hyT
  have hspan : ∀ x ∈ Submodule.span K {y}, Q x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [Q.map_smul, hy, smul_zero]
  have hjoin : ∀ x ∈ C ⊔ Submodule.span K {y}, Q x = 0 := by
    apply singular_sup Q C _ hC hspan
    intro x hx z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_smul, hCy x hx, smul_zero]
  obtain ⟨M, hJM, hM⟩ := exists_maximal_ge Q _ hjoin
  have hCM : C ≤ M := (show C ≤ C ⊔ Submodule.span K {y} from le_sup_left).trans hJM
  have hyM : y ∈ M := hJM ((show Submodule.span K {y} ≤ C ⊔ Submodule.span K {y} from le_sup_right)
    (Submodule.mem_span_singleton_self y))
  have hSTC : S ⊓ T ≤ C := by
    intro x hx
    exact ⟨hx.1, polar_zero_of_singular Q T hT.1 y x hyT hx.2⟩
  have hle : S ⊓ T ≤ M ⊓ T := fun x hx => ⟨hCM (hSTC hx), hx.2⟩
  have hnle : ¬ M ⊓ T ≤ S ⊓ T := fun h => hyS (h ⟨hyM, hyT⟩).1
  refine ⟨M, hM, ?_, lt_of_le_not_ge hle hnle⟩
  have hc := finrank_inf_ker_add_one_ge S phi
  change Module.finrank K S ≤ Module.finrank K C + 1 at hc
  have hm := Submodule.finrank_mono (show C ≤ S ⊓ M from le_inf hCS hCM)
  omega

abbrev MaximalSpaces (Q : QuadraticForm K V) := {S : Submodule K V // MaximalSingular Q S}

def GalleryStep (Q : QuadraticForm K V) (S T : MaximalSpaces Q) : Prop :=
  Module.finrank K S.val ≤ Module.finrank K (S.val ⊓ T.val : Submodule K V) + 1

theorem gallery_connected (Q : QuadraticForm K V) (S T : MaximalSpaces Q) :
    Relation.ReflTransGen (GalleryStep Q) S T := by
  suffices hall : ∀ n, ∀ S : MaximalSpaces Q,
      Module.finrank K T.val - Module.finrank K (S.val ⊓ T.val : Submodule K V) = n →
        Relation.ReflTransGen (GalleryStep Q) S T by
    exact hall _ S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn
    by_cases he : S = T
    · subst S
      exact Relation.ReflTransGen.refl
    · have hnot : ¬ T.val ≤ S.val := by
        intro h
        exact he (Subtype.ext (T.property.2 S.val S.property.1 h))
      obtain ⟨y, hyT, hyS⟩ := Set.not_subset.mp hnot
      obtain ⟨M, hM, hadj, hgain⟩ := maximal_exchange_towards Q S.val T.val S.property T.property y hyT hyS
      let R : MaximalSpaces Q := ⟨M, hM⟩
      have hstep : GalleryStep Q S R := hadj
      have hltcap := Submodule.finrank_lt_finrank_of_lt hgain
      have hcap := Submodule.finrank_mono (inf_le_right : M ⊓ T.val ≤ T.val)
      have hlt : Module.finrank K T.val - Module.finrank K (M ⊓ T.val : Submodule K V) < n := by
        rw [← hn]
        omega
      exact (Relation.ReflTransGen.single hstep).trans (ih _ hlt R rfl)

theorem galleryStep_finrank_mono (Q : QuadraticForm K V) (S T : MaximalSpaces Q)
    (hstep : GalleryStep Q S T) : Module.finrank K S.val ≤ Module.finrank K T.val := by
  by_cases he : S = T
  · subst T
    exact le_rfl
  have hstrict : (S.val ⊓ T.val : Submodule K V) < T.val := by
    apply lt_of_le_of_ne inf_le_right
    intro hcap
    have hTS : T.val ≤ S.val := hcap.ge.trans inf_le_left
    exact he (Subtype.ext (T.property.2 S.val S.property.1 hTS))
  have hd := Submodule.finrank_lt_finrank_of_lt hstrict
  change Module.finrank K S.val ≤ Module.finrank K (S.val ⊓ T.val : Submodule K V) + 1 at hstep
  omega

theorem maximal_finrank_le (Q : QuadraticForm K V) (S T : MaximalSpaces Q) :
    Module.finrank K S.val ≤ Module.finrank K T.val := by
  have hpath := gallery_connected Q S T
  induction hpath with
  | refl => exact le_rfl
  | @tail B C _ hBC ih => exact ih.trans (galleryStep_finrank_mono Q B C hBC)

theorem maximal_finrank_eq (Q : QuadraticForm K V) (S T : MaximalSpaces Q) :
    Module.finrank K S.val = Module.finrank K T.val :=
  Nat.le_antisymm (maximal_finrank_le Q S T) (maximal_finrank_le Q T S)

end SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalSingularGallery
