import SymmetricSubgroupAsymptotics.CFSGInjectiveCenterImage
import Mathlib.GroupTheory.Sylow

/-! Conjugate intrinsic centres of a Sylow subgroup form an actual
automorphism-stable subgroup family. This uses conjugacy of literal
Sylows, not preservation of an externally named root subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGSylowCentreFamily

def ambientCenter {G : Type*} [Group G] (P : Subgroup G) : Subgroup G :=
  (Subgroup.center P).map P.subtype

theorem map_ambientCenter {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (P : Subgroup G) :
    (ambientCenter P).map f = ambientCenter (P.map f) := by
  have he := CFSGInjectiveCenterImage.center_image (f.comp P.subtype)
    (hf.comp Subtype.val_injective)
  have hr : (f.comp P.subtype).range = P.map f := by
    rw [MonoidHom.range_comp, P.range_subtype]
  have hc := congrArg (fun S : Subgroup H => ambientCenter S) hr
  change (Subgroup.center P).map (f.comp P.subtype) =
    ambientCenter (f.comp P.subtype).range at he
  change ((Subgroup.center P).map P.subtype).map f = _
  rw [Subgroup.map_map]
  exact he.trans hc

theorem conjugate_centres_stable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (f : MulAut G) (g : G) :
    ∃ h : G, (ambientCenter (P : Subgroup G)).map (MulAut.conj h).toMonoidHom =
      ((ambientCenter (P : Subgroup G)).map (MulAut.conj g).toMonoidHom).map f.toMonoidHom := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P (f • (g • P))
  have he := congrArg (fun S : Sylow p G => (S : Subgroup G)) hh
  change (P : Subgroup G).map (MulAut.conj h).toMonoidHom =
    ((P : Subgroup G).map (MulAut.conj g).toMonoidHom).map f.toMonoidHom at he
  refine ⟨h, ?_⟩
  calc
    _ = ambientCenter ((P : Subgroup G).map (MulAut.conj h).toMonoidHom) :=
      map_ambientCenter _ (MulAut.conj h).injective _
    _ = ambientCenter (((P : Subgroup G).map (MulAut.conj g).toMonoidHom).map f.toMonoidHom) :=
      congrArg ambientCenter he
    _ = (ambientCenter ((P : Subgroup G).map (MulAut.conj g).toMonoidHom)).map f.toMonoidHom :=
      (map_ambientCenter _ f.injective _).symm
    _ = _ := congrArg (fun S : Subgroup G => S.map f.toMonoidHom)
      (map_ambientCenter _ (MulAut.conj g).injective _).symm

end SymmetricSubgroupAsymptotics.CFSGSylowCentreFamily
