import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSLDouble
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryGroup

/-! The checked literal SL double matrix also belongs to the actual C
elementary group. Only the common adjacent chain roots are used, so no
equality with a full symplectic group or alternate source is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSLDoubleEmbedding
open Matrix CFSGSymplecticSerreMatrices CFSGTypeAElementaryMatrices
variable (K : Type) [Field K] (r : ℕ)

theorem adjacent_elementary_mem (i j : Fin r) (hij : i≠j)
    (hadj : i.val+1=j.val ∨ j.val+1=i.val) (a : K) :
    CFSGOrthogonalDGenerationSLDouble.doubleHom K r (elementary hij a) ∈
      elementaryRootGroup K r := by
  rcases hadj with hpos | hneg
  · have hi : i.val+1<r := by rw [hpos]; exact j.isLt
    have hn : (⟨i.val+1,hi⟩ : Fin r)=j := Fin.ext hpos
    have he : CFSGOrthogonalDGenerationSLDouble.doubleHom K r (elementary hij a)=
        rootTransvection K r false i a := by
      apply Units.ext
      rw [CFSGOrthogonalDGenerationSLDouble.doubleHom_elementary_val]
      change 1+a • CFSGOrthogonalDGenerationSLDouble.chainMatrix K r i j =
        1+a • positive K r i
      rw [positive,dif_pos hi,hn]
      rfl
    rw [he]
    exact rootTransvection_mem K r false i a
  · have hj : j.val+1<r := by rw [hneg]; exact i.isLt
    have hn : (⟨j.val+1,hj⟩ : Fin r)=i := Fin.ext hneg
    have he : CFSGOrthogonalDGenerationSLDouble.doubleHom K r (elementary hij a)=
        rootTransvection K r true j a := by
      apply Units.ext
      rw [CFSGOrthogonalDGenerationSLDouble.doubleHom_elementary_val]
      change 1+a • CFSGOrthogonalDGenerationSLDouble.chainMatrix K r i j =
        1+a • negative K r j
      simp only [negative,positive,dif_pos hj,hn,Matrix.transpose_sub,
        Matrix.transpose_single,CFSGOrthogonalDGenerationSLDouble.chainMatrix]
    rw [he]
    exact rootTransvection_mem K r true j a

theorem doubleHom_range_le :
    (CFSGOrthogonalDGenerationSLDouble.doubleHom K r).range ≤ elementaryRootGroup K r := by
  let H := (elementaryRootGroup K r).comap (CFSGOrthogonalDGenerationSLDouble.doubleHom K r)
  have ht : H=⊤ := CFSGOrthogonalDGenerationAdjacentSL.eq_top_of_adjacent r H
    (fun i j hij hadj a => adjacent_elementary_mem K r i j hij hadj a)
  rintro _ ⟨A,rfl⟩
  change A∈H
  rw [ht]
  trivial

def doubleIntoElementary : Matrix.SpecialLinearGroup (Fin r) K →* elementaryRootGroup K r :=
  (CFSGOrthogonalDGenerationSLDouble.doubleHom K r).codRestrict _
    (fun A => doubleHom_range_le K r ⟨A,rfl⟩)

theorem doubleIntoElementary_injective : Function.Injective (doubleIntoElementary K r) := by
  intro A B h
  have hm := congrArg (fun u : elementaryRootGroup K r =>
    Matrix.toBlocks₁₁ (u.val : Mat K r)) h
  change A.val=B.val at hm
  exact Subtype.ext hm

end SymmetricSubgroupAsymptotics.CFSGSymplecticSLDoubleEmbedding
