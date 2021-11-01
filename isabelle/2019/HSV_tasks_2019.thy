theory HSV_tasks_2019 imports Main begin

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

section \<open>Starting point for Task 8\<close>

text \<open>The following function calculates the area of a circuit (i.e. number of gates).\<close>

fun area :: "circuit \<Rightarrow> nat" where
  "area (NOT c) = 1 + area c"
| "area (AND c1 c2) = 1 + area c1 + area c2"
| "area (OR c1 c2) = 1 + area c1 + area c2"
| "area _ = 0"

end