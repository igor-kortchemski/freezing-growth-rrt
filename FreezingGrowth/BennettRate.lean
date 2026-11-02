module

public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! The rate function in Proposition 3.1 of `main.tex`. -/

@[expose] public section

namespace FreezingGrowth

/-- Bennett's rate, used by the paper on positive arguments. -/
noncomputable def bennettRate (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) - u

end FreezingGrowth
