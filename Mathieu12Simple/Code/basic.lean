import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathieu12Simple.GDelone.basic
import Mathieu12Simple.GPseudoMetricSpace.GIsometry

-- a codeword is an element of Ω^|ι|, with hamming distance
abbrev HammingCodeWord (ι:Type*) [Fintype ι] (Ω:Type*) [DecidableEq Ω] := Hamming (Function.const ι Ω)

abbrev HammingCode (ι:Type*) [Fintype ι] (Ω:Type*) [DecidableEq Ω] := Set (HammingCodeWord ι Ω)

section
variable (β:Type*) [CompleteLattice β] [LinearOrderedAddCommMonoid β]
  {α₁:Type*} [GMetricSpace α₁ β]
  {α₂:Type*} [GMetricSpace α₂ β]


structure CodeHom (c₁:GDeloneSet α₁ β) (c₂:GDeloneSet α₂ β) where
  toFun : α₁ → α₂
  map_code : ∀ x ∈ c₁, toFun x ∈ c₂
  isometry: GIsometry β toFun

@[ext]
theorem CodeHom.ext {c₁:GDeloneSet α₁ β} {c₂:GDeloneSet α₂ β}
  (φ₁:CodeHom β c₁ c₂) (φ₂:CodeHom β c₁ c₂)
  (h: φ₁.toFun = φ₂.toFun): φ₁=φ₂ := by
  cases φ₁; cases φ₂; congr

instance (c₁:GDeloneSet α₁ β) (c₂:GDeloneSet α₂ β):
  FunLike (CodeHom β c₁ c₂) α₁ α₂ where
    coe := CodeHom.toFun
    coe_injective' := by
      intro φ₁ φ₂ hx
      aesop

structure CodeEquiv (c₁:GDeloneSet α₁ β) (c₂:GDeloneSet α₂ β) extends CodeHom β c₁ c₂ where
  toEquiv: α₁≃α₂
  map_is_equiv : (toEquiv:α₁→α₂) = toFun
  map_code_surjective: ∀ y∈c₂,∃ x ∈ c₁, toFun x = y
end

section
variable (K:Type*) [Field K]
  (V :Type*) [AddCommGroup V] [Module K V]
  (β :Type*)[LinearOrderedAddCommMonoid β] [CompleteLattice β]
  [GMetricSpace V β]

structure LinearCode where
  carrier : Set V
  toSubmodule:Submodule K V
  submodule_carrier_eq_carrier : toSubmodule.carrier = carrier
  toGDeloneSet : GDeloneSet V β
  gdeloneset_carrier_eq_carrier : toGDeloneSet.carrier = carrier

@[ext]
theorem LinearCode.ext (lc₁:LinearCode K V β) (lc₂:LinearCode K V β) (h:lc₁.carrier = lc₂.carrier) : lc₁=lc₂:= by
  cases lc₁ ; cases lc₂ ; congr
  . aesop
  . ext x ; simp_all only

instance: SetLike (LinearCode K V β) V where
    coe := fun c => c.carrier
    coe_injective' := fun φ₁ φ₂ hφ => by aesop -- don't worry about it

end
section
variable
  {K:Type*} [Field K]
  {β :Type*} [LinearOrderedAddCommMonoid β] [CompleteLattice β]
  {V₁ :Type*} [AddCommGroup V₁] [Module K V₁] [GMetricSpace V₁ β]
  {V₂ :Type*} [AddCommGroup V₂] [Module K V₂] [GMetricSpace V₂ β]

structure LinearCodeHom (lc₁:LinearCode K V₁ β) (lc₂:LinearCode K V₂ β) where
  toFun : V₁ → V₂
  toCodeHom : CodeHom β lc₁.toGDeloneSet lc₂.toGDeloneSet
  codehom_map_eq_map : toCodeHom.toFun = toFun
  toLinearMap : V₁ →ₗ[K] V₂
  linear_map_eq_map : toLinearMap.toFun = toFun



@[ext]
theorem LinearCodeHom.ext {lc₁:LinearCode K V₁ β} {lc₂:LinearCode K V₂ β}
  (φ₁:LinearCodeHom lc₁ lc₂) (φ₂:LinearCodeHom lc₁ lc₂) (h: φ₁.toFun = φ₂.toFun) : φ₁=φ₂ := by
  cases φ₁; cases φ₂;
  aesop -- don't worry about it


instance (lc₁:LinearCode K V₁ β) (lc₂:LinearCode K V₂ β): FunLike (LinearCodeHom lc₁ lc₂) V₁ V₂ where
  coe := fun φ => φ.toFun
  coe_injective' := by
    intro φ₁ φ₂ hφ
    aesop

end

structure LinearCodeEquiv
  {K:Type*} [Field K]
  {β :Type*} [LinearOrderedAddCommMonoid β] [CompleteLattice β]
  {V₁ :Type*} [AddCommGroup V₁] [Module K V₁] [GMetricSpace V₁ β] (lc₁:LinearCode K V₁ β)
  {V₂ :Type*} [AddCommGroup V₂] [Module K V₂] [GMetricSpace V₂ β] (lc₂:LinearCode K V₂ β)
  extends LinearCodeHom lc₁ lc₂ where
  toEquiv: V₁ ≃ V₂
  map_is_equiv : (toEquiv:V₁→V₂) = toFun
  map_code_surjective: ∀ y∈lc₂,∃ x ∈ lc₁, toFun x = y

namespace Code
variable {ι:Type*} [Fintype ι] {Ω:Type*} [DecidableEq Ω] (C:Code ι Ω)
abbrev NonTrivialCode : Prop := GDeloneSet (C: Set (CodeWord ι Ω))
-- DeloneSet means: Half the shortest nontrivial distance is

-- minimal distance of a code (with at least two elements)
-- is the smallest hamming distance between separate words
noncomputable def minimal_distance : ℝ := (C:Set (CodeWord ι Ω)).infsep

-- improve by not requiring Fintype Ω and changing ℝ to ENNReal?
noncomputable def dimension [Fintype Ω] : ℝ := Real.log C.card / (Real.log ((@Finset.univ Ω).card))

noncomputable def rate [Fintype Ω] : ℝ := dimension C / (@Finset.univ ι).card

-- theorem hamming_bound [Fintype Ω]: ∀ (c:Code ι Ω), rate c ≤ 1 - (Real.log (||)) / () := sorry


end Code
