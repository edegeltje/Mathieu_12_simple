import Mathieu12Simple.Code.Hamming

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
