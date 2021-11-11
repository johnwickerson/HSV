theory HSV_tasks_2021 imports Complex_Main begin

section \<open>Task 1: Factorising circuits.\<close>

(* Datatype for representing simple circuits. *)
datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

(* Simulates a circuit given a valuation for each input wire. *)
fun simulate where
  "simulate (AND c1 c2) \<rho> = ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>))"
| "simulate (OR c1 c2) \<rho> = ((simulate c1 \<rho>) \<or> (simulate c2 \<rho>))"
| "simulate (NOT c) \<rho> = (\<not> (simulate c \<rho>))"
| "simulate TRUE \<rho> = True"
| "simulate FALSE \<rho> = False"
| "simulate (INPUT i) \<rho> = \<rho> i"

(* Equivalence between circuits. *)
fun circuits_equiv (infix "\<sim>" 50) (* the "50" indicates the operator precedence *) where
  "c1 \<sim> c2 = (\<forall>\<rho>. simulate c1 \<rho> = simulate c2 \<rho>)"

(* An optimisation that exploits the following Boolean identities:
  `(a | b) & (a | c) = a | (b & c)`
  `(a | b) & (c | a) = a | (b & c)`
  `(a | b) & (b | c) = b | (a & c)`
  `(a | b) & (c | b) = b | (a & c)`
 *)
fun factorise where
  "factorise (NOT c) = NOT (factorise c)"
| "factorise (AND (OR c1 c2) (OR c3 c4)) = (
    let c1' = factorise c1; c2' = factorise c2; c3' = factorise c3; c4' = factorise c4 in
    if c1' = c3' then OR c1' (AND c2' c4') 
    else if c1' = c4' then OR c1' (AND c2' c3') 
    else if c2' = c3' then OR c2' (AND c1' c4') 
    else if c2' = c4' then OR c2' (AND c1' c3') 
    else AND (OR c1' c2') (OR c3' c4'))"
| "factorise (AND c1 c2) = AND (factorise c1) (factorise c2)"
| "factorise (OR c1 c2) = OR (factorise c1) (factorise c2)"
| "factorise TRUE = TRUE"
| "factorise FALSE = FALSE"
| "factorise (INPUT i) = INPUT i"

lemma (* test case *)
 "factorise (AND TRUE TRUE) = AND TRUE TRUE"
  by eval
lemma (* test case *)
  "factorise (AND (OR (INPUT 1) FALSE) (OR TRUE (INPUT 1))) = 
  OR (INPUT 1) (AND FALSE TRUE)"
  by eval
lemma (* test case *)
  "factorise (NOT (AND (OR FALSE (INPUT 2)) (OR TRUE (INPUT 2)))) =
  NOT (OR (INPUT 2) (AND FALSE TRUE))"
  by eval

theorem factorise_is_sound: "factorise c \<sim> c"
  sorry

fun factorise2 where "factorise2 c = c" (* dummy definition *)

lemma (* test case *)
  "factorise2 (OR (AND (INPUT 1) (INPUT 2)) (AND TRUE (INPUT 1))) = 
  AND (INPUT 1) (OR (INPUT 2) TRUE)"
  sorry

theorem factorise2_is_sound: "factorise2 c \<sim> c"
  sorry

section \<open>Task 2: A theorem about divisibility.\<close>

(* NB: Without the "::int" annotation, Isabelle will try to prove a 
   slightly more general theorem where "a" and "b" can be either ints
   or nats. That more general theorem is a little harder to prove. *)
theorem plus_dvd_odd_power:
  "(a::int) + b dvd a ^ (2 * n + 1) + b ^ (2 * n + 1)"
  sorry


section \<open>Task 3: Proving that the shift-and-add-3 algorithm is correct.\<close>

subsection \<open>Binary and its conversion to nat\<close>

type_synonym bit = "bool"

abbreviation B0 where "B0 == False"
abbreviation B1 where "B1 == True"


fun binary_to_nat :: "bit list \<Rightarrow> nat"
where
  "binary_to_nat [] = 0"
| "binary_to_nat (b # bs) = (if b then 2 ^ length bs else 0) + binary_to_nat bs"


lemma (* test case *) "binary_to_nat [B0, B1, B0, B1] = 5" by eval
lemma (* test case *) "binary_to_nat [B0, B0, B1, B0, B1] = 5" by eval
lemma (* test case *) "binary_to_nat [B1] = 1" by eval
lemma (* test case *) "binary_to_nat [B0] = 0" by eval

subsection \<open>BCD and its conversion to nat\<close>

type_synonym nibble = "bit * bit * bit * bit"

fun nibble_to_nat :: "nibble \<Rightarrow> nat"
where
  "nibble_to_nat (B0,B0,B0,B0) = 0"
| "nibble_to_nat (B0,B0,B0,B1) = 1"
| "nibble_to_nat (B0,B0,B1,B0) = 2"
| "nibble_to_nat (B0,B0,B1,B1) = 3"
| "nibble_to_nat (B0,B1,B0,B0) = 4"
| "nibble_to_nat (B0,B1,B0,B1) = 5"
| "nibble_to_nat (B0,B1,B1,B0) = 6"
| "nibble_to_nat (B0,B1,B1,B1) = 7"
| "nibble_to_nat (B1,B0,B0,B0) = 8"
| "nibble_to_nat (B1,B0,B0,B1) = 9"
| "nibble_to_nat (B1,B0,B1,B0) = 10"
| "nibble_to_nat (B1,B0,B1,B1) = 11"
| "nibble_to_nat (B1,B1,B0,B0) = 12"
| "nibble_to_nat (B1,B1,B0,B1) = 13"
| "nibble_to_nat (B1,B1,B1,B0) = 14"
| "nibble_to_nat (B1,B1,B1,B1) = 15"

fun bcd_to_nat :: "nibble list \<Rightarrow> nat"
where
  "bcd_to_nat [] = 0"
| "bcd_to_nat (n # ns) = bcd_to_nat ns + nibble_to_nat n * 10 ^ length ns"

lemma (* test case *) "bcd_to_nat [(B0,B1,B1,B0)] = 6" by eval
lemma (* test case *) "bcd_to_nat [(B0,B1,B1,B0),(B1,B0,B0,B1)] = 69" by eval
lemma (* test case *) "bcd_to_nat [(B0,B0,B0,B0),(B1,B0,B0,B1)] = 9" by eval
lemma (* test case *) "bcd_to_nat [(B0,B0,B1,B1),(B0,B0,B0,B0)] = 30" by eval


subsection \<open>Converting binary to BCD\<close>

fun binary_to_bcd :: "bit list \<Rightarrow> nibble list"
where
  "binary_to_bcd bs = []" (* dummy definition *)  

lemma (* test case *)
  "binary_to_bcd [B1,B0,B1,B0,B1,B0,B1] = [(B1,B0,B0,B0), (B0,B1,B0,B1)]" 
  sorry

subsection \<open>Checking that nibbles correspond to valid BCD digits\<close>

fun valid_nibble :: "nibble \<Rightarrow> bool"
where
  "valid_nibble (B0,B0,B0,B0) = True"
| "valid_nibble (B0,B0,B0,B1) = True"
| "valid_nibble (B0,B0,B1,B0) = True"
| "valid_nibble (B0,B0,B1,B1) = True"
| "valid_nibble (B0,B1,B0,B0) = True"
| "valid_nibble (B0,B1,B0,B1) = True"
| "valid_nibble (B0,B1,B1,B0) = True"
| "valid_nibble (B0,B1,B1,B1) = True"
| "valid_nibble (B1,B0,B0,B0) = True"
| "valid_nibble (B1,B0,B0,B1) = True"
| "valid_nibble (B1,B0,B1,B0) = False"
| "valid_nibble (B1,B0,B1,B1) = False"
| "valid_nibble (B1,B1,B0,B0) = False"
| "valid_nibble (B1,B1,B0,B1) = False"
| "valid_nibble (B1,B1,B1,B0) = False"
| "valid_nibble (B1,B1,B1,B1) = False"

theorem binary_to_bcd_valid:
  "list_all valid_nibble (binary_to_bcd bs)"
  sorry
  
subsection \<open>Proof that the binary_to_bcd translation is correct.\<close>

theorem binary_to_bcd_correct:
  "bcd_to_nat (binary_to_bcd bs) = binary_to_nat bs"
  sorry

end