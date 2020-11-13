theory HSV_tasks_2019_solutions_task11 imports Main begin

section \<open>Representation of circuits.\<close>

text \<open>A wire is represented as an integer.\<close>

type_synonym wire = int

datatype gate =
  NOT "wire" "wire"
| AND "wire" "wire" "wire"
| OR "wire" "wire" "wire"
| TRUE "wire"
| FALSE "wire"

text \<open>A circuit is represented as a list gates together with a list of output wires.\<close>

type_synonym circuit = "gate list \<times> wire list"

text \<open>Here are some examples of circuits.\<close>

definition "circuit1 == ([NOT 1 2], [2])"
definition "circuit2 == ([NOT 1 3, NOT 2 4, AND 3 4 5, NOT 5 6], [6])"
definition "circuit3 == ([NOT 1 3, NOT 2 4, NOT 1 7, AND 3 4 5, NOT 5 6], [6])"
definition "circuit4 == ([NOT 1 3, NOT 2 4, NOT 1 7, NOT 7 8, AND 3 4 5, NOT 5 6], [6])"

text \<open>Return the input wire(s) of a gate.\<close>

fun inputs_of where
  "inputs_of (NOT wi _) = {wi}"
| "inputs_of (AND wi1 wi2 _) = {wi1, wi2}"
| "inputs_of (OR wi1 wi2 _) = {wi1, wi2}"
| "inputs_of (TRUE _) = {}"
| "inputs_of (FALSE _) = {}"

text \<open>Return the output wire of a gate.\<close>

fun output_of where
  "output_of (NOT _ wo) = wo"
| "output_of (AND _ _ wo) = wo"
| "output_of (OR _ _ wo) = wo"
| "output_of (TRUE wo) = wo"
| "output_of (FALSE wo) = wo"

section \<open>Evaluating circuits.\<close>

text \<open>A valuation associates every wire with a truth-value.\<close>

type_synonym valuation = "wire \<Rightarrow> bool"

text \<open>A few examples of valuations.\<close>

definition "\<rho>0 == \<lambda>_. True"
definition "\<rho>1 == \<rho>0(1 := True, 2 := False, 3 := True)"
definition "\<rho>2 == \<rho>0(1 := True, 2 := True, 3 := True)"

text \<open>Calculate the output of a single gate, given a valuation.\<close>

fun sim_gate :: "valuation \<Rightarrow> gate \<Rightarrow> bool" where
  "sim_gate \<rho> (NOT wi wo) = (\<not> \<rho> wi)"
| "sim_gate \<rho> (AND wi1 wi2 wo) = (\<rho> wi1 \<and> \<rho> wi2)"
| "sim_gate \<rho> (OR wi1 wi2 wo) = (\<rho> wi1 \<or> \<rho> wi2)"
| "sim_gate \<rho> (TRUE wo) = True"
| "sim_gate \<rho> (FALSE wo) = False"

text \<open>Simulates a list of gates, given an initial valuation. Produces a new valuation.\<close>

fun sim_gates :: "valuation \<Rightarrow> gate list \<Rightarrow> valuation" where
  "sim_gates \<rho> [] = \<rho>"
| "sim_gates \<rho> (g # gs) = sim_gates (\<rho> (output_of g := sim_gate \<rho> g)) gs"

text \<open>Simulates a circuit, given an initial valuation. Produces a list of 
      truth-values, one truth-value per output.\<close>

fun sim :: "valuation \<Rightarrow> circuit \<Rightarrow> bool list" where
  "sim \<rho> (gs, wos) = map (sim_gates \<rho> gs) wos"

text \<open>Testing the simulator.\<close>

value "sim \<rho>1 circuit1"
value "sim \<rho>2 circuit1"
value "sim \<rho>1 circuit2"
value "sim \<rho>2 circuit2"
value "sim \<rho>1 circuit3"
value "sim \<rho>2 circuit3"

section \<open>Optimising circuits by removing dead gates.\<close>

text \<open>Return the set of wires that lead to an output.\<close>

fun live_wires where
  "live_wires ([], wos) = set wos"
| "live_wires (g # gs, wos) = (let ws = live_wires (gs, wos) in
     (if output_of g \<in> ws then inputs_of g else {}) \<union> ws)"

value "live_wires ([NOT 1 3, NOT 2 4, NOT 1 7, AND 3 4 5, NOT 5 6], [6])"
value "live_wires ([NOT 1 3, NOT 2 4, NOT 1 7, NOT 7 8, AND 3 4 5, NOT 5 6], [6])"
value "live_wires ([NOT 1 3, NOT 2 4, NOT 1 7, NOT 7 8, AND 3 4 5, NOT 5 6], [6, 8])"
value "live_wires ([NOT 1 3, NOT 2 4, NOT 7 8, AND 3 4 5, NOT 5 6], [6])"

text \<open>This is a helper function for the next function .\<close>

fun remove_dead_inner where
  "remove_dead_inner [] wos = []" 
| "remove_dead_inner (g # gs) wos = 
   (let gs' = remove_dead_inner gs wos in 
   (if output_of g \<in> live_wires (gs', wos) then [g] else []) @ gs')"

text \<open>This function strips out gates that are not needed.\<close>

fun remove_dead where
  "remove_dead (gs, wos) = (remove_dead_inner gs wos, wos)"

value "remove_dead circuit2"
value "remove_dead circuit3"
value "remove_dead circuit4"

section \<open>Proving that removing dead gates does not change a circuit's behaviour.\<close>

text \<open>This lemma is obviously false -- it wrongly claims that remove_dead
      has no effect on a circuit.\<close>

lemma "remove_dead c = c" oops

text \<open>We shall say that two functions are 'congruent on X' if they coincide on all inputs in X.\<close>

fun cong_on where
  "cong_on X f g = (\<forall>x \<in> X. f x = g x)"

text \<open>Congruency is transitive.\<close>

lemma cong_on_trans:
  assumes "cong_on X g h"
  assumes "cong_on X f g"
  shows "cong_on X f h"
  using assms by simp

text \<open>This is a rather technical lemma. It says that if two valuations \<rho> and \<rho>' are
      congruent on all wires that are live in circuit (g # gs, wos), then the 
      respective valuations obtained after simulating g remain congruent on all wires 
      that are live in circuit (gs, wos). \<close>

lemma cong_on_live_wires:
  assumes "cong_on (live_wires (g # gs, wos)) \<rho> \<rho>'"
  shows "cong_on (live_wires (gs, wos)) (\<rho>(output_of g := sim_gate \<rho> g)) (\<rho>'(output_of g := sim_gate \<rho>' g))"
  using assms
  apply (cases "output_of g \<in> live_wires (gs, wos)", auto)
  apply (cases g, auto)+
  done

text \<open>If valuations \<rho> and \<rho>' are congruent on all wires that are live in circuit (gs, wos), then
      the respective valuations obtained after simulating gs are congruent on all wires in wos.\<close> 

lemma cong_sim_gates:
  assumes "cong_on (live_wires (gs, wos)) \<rho> \<rho>'"
  shows "cong_on (set wos) (sim_gates \<rho> gs) (sim_gates \<rho>' gs)"
  using assms
proof (induct gs arbitrary: \<rho> \<rho>')
  case Nil
  thus ?case by auto
next
  case (Cons g gs)
  show ?case 
    apply (clarsimp simp del: cong_on.simps) 
    apply (rule Cons.hyps[OF cong_on_live_wires[OF Cons.prems]]) 
    done
qed

text \<open>This is a slightly unwrapped version of the main theorem below.\<close>

lemma sim_remove_dead:
  "cong_on (set wos) (sim_gates \<rho> (remove_dead_inner gs wos)) (sim_gates \<rho> gs)"
proof (induct gs arbitrary: \<rho>)
  case Nil
  thus ?case by simp
next 
  case (Cons g gs \<rho>)
  show ?case
  proof (cases "output_of g \<in> live_wires (remove_dead (gs, wos))")
    case True
    thus ?thesis using Cons.hyps by auto
  next
    case False
    thus ?thesis 
      apply (simp del: cong_on.simps)
      apply (rule cong_on_trans)
       apply (rule Cons.hyps[of "\<rho>(output_of g := sim_gate \<rho> g)"])
      apply (rule cong_sim_gates)    
      apply clarsimp 
      done
  qed
qed

text \<open>We define a convenient shorthand for expressing that two circuits have the same behaviour.\<close>

fun sim_equiv (infix "\<sim>" 50) where
  "c1 \<sim> c2 = (\<forall>\<rho>. sim \<rho> c1 = sim \<rho> c2)"

text \<open>Main theorem: removing the dead gates from a circuit does not change its behaviour.\<close>

theorem "remove_dead c \<sim> c"
  using sim_remove_dead by (cases c, auto)

end