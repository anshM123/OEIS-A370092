import DMSolutions.OEIS_A370092.Solution

/-!
# Checks for the solution of `OeisA370092.bounds`

* The definitions copied into `A370092Core` are the statement file's definitions (`rfl`).
* `bounds_solved` has exactly the type of the repository statement `bounds`.
* `bounds_solved` uses only the standard axioms.
-/

-- The copied definitions agree with the statement file's definitions.
example : OeisA370092.a = A370092Core.a := by with_unfolding_all rfl
example : @OeisA370092.eventually_periodic = @A370092Core.eventually_periodic := rfl
example : OeisA370092.a_mod_k = A370092Core.a_mod_k := by with_unfolding_all rfl

-- `bounds_solved` has exactly the type of the repository statement `bounds`.
example : type_of% @OeisA370092.bounds = type_of% @OeisA370092.bounds_solved := rfl

-- The repository statement and ours, printed for comparison:
#check @OeisA370092.bounds
#check @OeisA370092.bounds_solved

#print axioms OeisA370092.bounds_solved
