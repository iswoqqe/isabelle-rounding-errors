theory RoundingErrors
  imports Complex_Main "HOL-Library.Extended_Real" "HOL-Analysis.Convex"
begin

section \<open>Input Language and Semantics\<close>

datatype 's Expr =
  Add "'s Expr" "'s Expr" |
  Mul "'s Expr" "'s Expr" |
  Div "'s Expr" "'s Expr" |
  Neg "'s Expr" |
  Rnd "'s Expr" 's |
  Const "real" |
  Var nat

text \<open>We use relations (and not functions) for the semantics to avoid division-by-zero issues\<close>

inductive exact_eval :: "(nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> real \<Rightarrow> bool" where
  "exact_eval I lhs l \<Longrightarrow> exact_eval I rhs r \<Longrightarrow> exact_eval I (Add lhs rhs) (l + r)" |
  "exact_eval I lhs l \<Longrightarrow> exact_eval I rhs r \<Longrightarrow> exact_eval I (Mul lhs rhs) (l * r)" |
  "exact_eval I lhs l \<Longrightarrow> exact_eval I rhs r \<Longrightarrow> r \<noteq> 0 \<Longrightarrow> exact_eval I (Div lhs rhs) (l / r)" |
  "exact_eval I ex e \<Longrightarrow> exact_eval I (Neg ex) (-e)" |
  "exact_eval I ex e \<Longrightarrow> exact_eval I (Rnd ex s) e" |
  "exact_eval I (Const c) c" |
  "exact_eval I (Var x) (I x)"

inductive rnd_eval :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> real \<Rightarrow> bool" where
  "rnd_eval p I lhs l \<Longrightarrow> rnd_eval p I rhs r \<Longrightarrow> rnd_eval p I (Add lhs rhs) (l + r)" |
  "rnd_eval p I lhs l \<Longrightarrow> rnd_eval p I rhs r \<Longrightarrow> rnd_eval p I (Mul lhs rhs) (l * r)" |
  "rnd_eval p I lhs l \<Longrightarrow> rnd_eval p I rhs r \<Longrightarrow> r \<noteq> 0 \<Longrightarrow> rnd_eval p I (Div lhs rhs) (l / r)" |
  "rnd_eval p I ex e \<Longrightarrow> rnd_eval p I (Neg ex) (-e)" |
  "rnd_eval p I ex e \<Longrightarrow> rnd_eval p I (Rnd ex s) (e + p e s)" |
  "rnd_eval p I (Const c) c" |
  "rnd_eval p I (Var x) (I x)"

inductive add_err :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> real \<Rightarrow> bool" where
"exact_eval I ex exact \<Longrightarrow> rnd_eval p I ex rnd
  \<Longrightarrow> add_err p I ex (rnd - exact)"

inductive rel_err :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> real \<Rightarrow> bool" where
"exact_eval I ex exact \<Longrightarrow> exact \<noteq> 0 \<Longrightarrow> rnd_eval p I ex rnd
  \<Longrightarrow> rel_err p I ex ((rnd - exact) / exact)"

subsection \<open>For better proof automation\<close>

declare exact_eval.intros [intro]
declare rnd_eval.intros [intro]
declare add_err.intros [intro]
declare rel_err.intros [intro]

inductive_cases exact_eval_AddE [elim!]: "exact_eval I (Add a b) v"
inductive_cases exact_eval_MulE [elim!]: "exact_eval I (Mul a b) v"
inductive_cases exact_eval_DivE [elim!]: "exact_eval I (Div a b) v"
inductive_cases exact_eval_NegE [elim!]: "exact_eval I (Neg a) v"
inductive_cases exact_eval_RndE [elim!]: "exact_eval I (Rnd a s) v"
inductive_cases exact_eval_ConstE [elim!]: "exact_eval I (Const c) v"
inductive_cases exact_eval_VarE [elim!]: "exact_eval I (Var x) v"

inductive_cases rnd_eval_AddE [elim!]: "rnd_eval p I (Add a b) v"
inductive_cases rnd_eval_MulE [elim!]: "rnd_eval p I (Mul a b) v"
inductive_cases rnd_eval_DivE [elim!]: "rnd_eval p I (Div a b) v"
inductive_cases rnd_eval_NegE [elim!]: "rnd_eval p I (Neg a) v"
inductive_cases rnd_eval_RndE [elim!]: "rnd_eval p I (Rnd a s) v"
inductive_cases rnd_eval_ConstE [elim!]: "rnd_eval p I (Const c) v"
inductive_cases rnd_eval_VarE [elim!]: "rnd_eval p I (Var x) v"

inductive_cases add_errE [elim!]: "add_err p I ex v"
inductive_cases rel_errE [elim!]: "rel_err p I ex v"

section \<open>Determinism and other useful lemmas\<close>

lemma exact_eval_unique [dest]: "exact_eval i ex e1 \<Longrightarrow> exact_eval i ex e2 \<Longrightarrow> e1 = e2"
  by (induction ex arbitrary: e1 e2) auto

lemma rnd_eval_unique [dest]: "rnd_eval p i ex e1 \<Longrightarrow> rnd_eval p i ex e2 \<Longrightarrow> e1 = e2"
  by (induction ex arbitrary: e1 e2) auto

lemma add_err_unique [dest]: "add_err p i ex a1 \<Longrightarrow> add_err p i ex a2 \<Longrightarrow> a1 = a2"
  by blast

lemma rel_err_unique [dest]: "rel_err p i ex r1 \<Longrightarrow> rel_err p i ex r2 \<Longrightarrow> r1 = r2"
  by blast

lemma rel_err_standard_form [dest]:
  assumes "exact_eval i ex e" and "rel_err p i ex r"
  shows "rnd_eval p i ex (e * (1 + r))"
proof -
  obtain f where f_def: "rnd_eval p i ex f" using assms by auto
  hence "r = (f - e) / e" using assms by auto
  moreover have "e \<noteq> 0" using assms by blast
  ultimately have "f = e * (1 + r)" using assms by (simp add: diff_divide_distrib)
  thus ?thesis using assms f_def by simp
qed

lemma rel_from_add_err:
  "exact_eval i ex e \<Longrightarrow> add_err p i ex a \<Longrightarrow> e \<noteq> 0 \<Longrightarrow> rel_err p i ex (a / e)"
  by blast

lemma add_from_rel_err:
  "exact_eval i ex e \<Longrightarrow> rel_err p i ex r \<Longrightarrow> add_err p i ex (r * e)"
  by force

(*subsection \<open>Functions might be more convenient to work with.\<close>

fun exact_value :: "(nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> real" where
"exact_value i (Add lhs rhs) = exact_value i lhs + exact_value i rhs" |
"exact_value i (Mul lhs rhs) = exact_value i lhs * exact_value i rhs" |
"exact_value i (Div lhs rhs) = exact_value i lhs / exact_value i rhs" |
"exact_value i (Neg ex) = -exact_value i ex" |
"exact_value i (Rnd ex s) = exact_value i ex" |
"exact_value i (Const c) = c" |
"exact_value i (Var x) = i x"

fun exact_wf :: "(nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> bool" where
"exact_wf i (Add lhs rhs) \<longleftrightarrow> exact_wf i lhs \<and> exact_wf i rhs" |
"exact_wf i (Mul lhs rhs) \<longleftrightarrow> exact_wf i lhs \<and> exact_wf i rhs" |
"exact_wf i (Div lhs rhs) \<longleftrightarrow> exact_wf i lhs \<and> exact_wf i rhs \<and> exact_value i rhs \<noteq> 0" |
"exact_wf i (Neg ex) \<longleftrightarrow> exact_wf i ex" |
"exact_wf i (Rnd ex s) \<longleftrightarrow> exact_wf i ex" |
"exact_wf i (Const c) \<longleftrightarrow> True" |
"exact_wf i (Var x) \<longleftrightarrow> True"

fun rnd_value :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> real" where
"rnd_value p i (Add lhs rhs) = rnd_value p i lhs + rnd_value p i rhs" |
"rnd_value p i (Mul lhs rhs) = rnd_value p i lhs * rnd_value p i rhs" |
"rnd_value p i (Div lhs rhs) = rnd_value p i lhs / rnd_value p i rhs" |
"rnd_value p i (Neg ex) = -rnd_value p i ex" |
"rnd_value p i (Rnd ex s) = rnd_value p i ex + p (rnd_value p i ex) s" |
"rnd_value p i (Const c) = c" |
"rnd_value p i (Var x) = i x"

fun rnd_wf :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> bool" where
"rnd_wf p i (Add lhs rhs) \<longleftrightarrow> rnd_wf p i lhs \<and> rnd_wf p i rhs" |
"rnd_wf p i (Mul lhs rhs) \<longleftrightarrow> rnd_wf p i lhs \<and> rnd_wf p i rhs" |
"rnd_wf p i (Div lhs rhs) \<longleftrightarrow> rnd_wf p i lhs \<and> rnd_wf p i rhs \<and> rnd_value p i rhs \<noteq> 0" |
"rnd_wf p i (Neg ex) \<longleftrightarrow> rnd_wf p i ex" |
"rnd_wf p i (Rnd ex s) \<longleftrightarrow> rnd_wf p i ex" |
"rnd_wf p i (Const c) \<longleftrightarrow> True" |
"rnd_wf p i (Var x) \<longleftrightarrow> True"

fun add_err_wf :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> bool" where
"add_err_wf p i ex \<longleftrightarrow> exact_wf i ex \<and> rnd_wf p i ex"

fun add_err_value :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> real" where
"add_err_value p i ex = rnd_value p i ex - exact_value i ex"

lemma exact_value_correct [dest]: "exact_wf i ex \<Longrightarrow> exact_eval i ex (exact_value i ex)"
  by (induction ex) auto

lemma rnd_value_correct [dest]: "rnd_wf p i ex \<Longrightarrow> rnd_eval p i ex (rnd_value p i ex)"
  by (induction ex) auto

lemma add_err_value_correct [dest]: "add_err_wf p i ex \<Longrightarrow> add_err p i ex (add_err_value p i ex)"
  by auto*)

section \<open>Error Propagation Lemmas\<close>

subsection \<open>Lemmas enabling any propagation equation to be used\<close>

text \<open>we use these template lemmas to separate two different concerns:
  (1) existence of the errors, and
  (2) the error propagation\<close>

lemma add_err_prop_add_template:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "add_err p i lhs a1" and "add_err p i rhs a2"
    and "(e1 + a1) + (e2 + a2) - (e1 + e2) = res"
  shows "add_err p i (Add lhs rhs) (res)"
proof -
  have "rnd_eval p i lhs (e1 + a1)" using assms by auto
  moreover have "rnd_eval p i rhs (e2 + a2)" using assms by auto
  ultimately have "rnd_eval p i (Add lhs rhs) ((e1 + a1) + (e2 + a2))" using assms by auto
  moreover have "exact_eval i (Add lhs rhs) (e1 + e2)" using assms by auto
  ultimately have "add_err p i (Add lhs rhs) ((e1 + a1) + (e2 + a2) - (e1 + e2))"
    using add_err.intros by metis
  thus ?thesis using assms by simp
qed

lemma add_err_prop_mul_template:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "add_err p i lhs a1" and "add_err p i rhs a2"
    and "(e1 + a1) * (e2 + a2) - (e1 * e2) = res"
  shows "add_err p i (Mul lhs rhs) res"
proof -
  have "rnd_eval p i lhs (e1 + a1)" using assms by auto
  moreover have "rnd_eval p i rhs (e2 + a2)" using assms by auto
  ultimately have "rnd_eval p i (Mul lhs rhs) ((e1 + a1) * (e2 + a2))" using assms by auto
  moreover have "exact_eval i (Mul lhs rhs) (e1 * e2)" using assms by auto
  ultimately have "add_err p i (Mul lhs rhs) ((e1 + a1) * (e2 + a2) - (e1 * e2))"
    using add_err.intros by metis
  thus ?thesis using assms by simp
qed

lemma add_err_prop_div_template:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "add_err p i lhs a1" and "add_err p i rhs a2"
    and "(e1 + a1) / (e2 + a2) - (e1 / e2) = res"
    and "e2 \<noteq> 0" and "e2 + a2 \<noteq> 0"
  shows "add_err p i (Div lhs rhs) res"
proof -
  have "rnd_eval p i lhs (e1 + a1)" using assms by auto
  moreover have "rnd_eval p i rhs (e2 + a2)" using assms by auto
  ultimately have "rnd_eval p i (Div lhs rhs) ((e1 + a1) / (e2 + a2))" using assms by auto
  moreover have "exact_eval i (Div lhs rhs) (e1 / e2)" using assms by auto
  ultimately have "add_err p i (Div lhs rhs) ((e1 + a1) / (e2 + a2) - (e1 / e2))"
    using add_err.intros by metis
  thus ?thesis using assms by simp
qed

(*
lemma add_err_prop_neg_template:
  assumes "exact_eval i ex e" and "add_err p i ex a"
    and "-(e + a) - (-e) = res"
  shows "add_err p i (Neg ex) res"
proof -
  have "rnd_eval p i (Neg ex) (-(e + a))" using assms by force
  moreover have "exact_eval i (Neg ex) (-e)" using assms by auto
  ultimately have "add_err p i (Neg ex) (-(e + a) - (-e))"
    using add_err.intros by metis
  thus ?thesis using assms by simp
qed
*)

lemma add_err_prop_rnd_template:
  assumes "exact_eval i ex e" and "add_err p i ex a"
    and "(e + a + p (e + a) s) - e = res"
  shows "add_err p i (Rnd ex s) res"
proof -
  have "rnd_eval p i (Rnd ex s) (e + a + p (e + a) s)" using assms by force
  moreover have "exact_eval i (Rnd ex s) e" using assms by blast
  ultimately have "add_err p i (Rnd ex s) (e + a + p (e + a) s - e)" using add_err.intros by metis
  thus ?thesis using assms by simp
qed

lemma rel_err_prop_add_template:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "rel_err p i lhs r1" and "rel_err p i rhs r2"
    and "e1 + e2 \<noteq> 0"
    and "(e1 * (1 + r1) + e2 *(1 + r2) - (e1 + e2)) / (e1 + e2) = res"
  shows "rel_err p i (Add lhs rhs) (res)"
proof -
  have "rnd_eval p i lhs (e1 * (1 + r1))" using assms by auto
  moreover have "rnd_eval p i rhs (e2 * (1 + r2))" using assms by auto
  ultimately have "rnd_eval p i (Add lhs rhs) (e1 * (1 + r1) + e2 * (1 + r2))" using assms by auto
  moreover have "exact_eval i (Add lhs rhs) (e1 + e2)" using assms by auto
  ultimately have "rel_err p i (Add lhs rhs) ((e1*(1 + r1) + e2*(1 + r2) - (e1 + e2)) / (e1 + e2))"
    by (simp add: assms(5) rel_err.intros)
  thus ?thesis using assms by simp
qed

lemma rel_err_prop_mul_template:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "rel_err p i lhs r1" and "rel_err p i rhs r2"
    and "e1 * e2 \<noteq> 0"
    and "(e1 * (1 + r1) * e2 *(1 + r2) - (e1 * e2)) / (e1 * e2) = res"
  shows "rel_err p i (Mul lhs rhs) (res)"
proof -
  have "rnd_eval p i lhs (e1 * (1 + r1))" using assms by auto
  moreover have "rnd_eval p i rhs (e2 * (1 + r2))" using assms by blast
  ultimately have "rnd_eval p i (Mul lhs rhs) (e1 * (1 + r1) * e2 * (1 + r2))"
    using mult.assoc rnd_eval.intros(2) by metis
  moreover have "exact_eval i (Mul lhs rhs) (e1 * e2)" using assms by auto
  ultimately have "rel_err p i (Mul lhs rhs) ((e1*(1 + r1) * e2*(1 + r2) - (e1 * e2)) / (e1 * e2))"
    using assms(5) rel_err.intros by metis
  thus ?thesis using assms by simp
qed

lemma rel_err_prop_div_template:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "rel_err p i lhs r1" and "rel_err p i rhs r2"
    and "e1 / e2 \<noteq> 0" and "e2 * (1 + r2) \<noteq> 0"
    and "(e1 * (1 + r1) / (e2 *(1 + r2)) - (e1 / e2)) / (e1 / e2) = res"
  shows "rel_err p i (Div lhs rhs) (res)"
proof -
  have "rnd_eval p i lhs (e1 * (1 + r1))" using assms rel_err_standard_form by metis
  moreover have "rnd_eval p i rhs (e2 * (1 + r2))" using assms rel_err_standard_form by metis
  ultimately have "rnd_eval p i (Div lhs rhs) (e1 * (1 + r1) / (e2 * (1 + r2)))"
    using assms by blast
  moreover have "exact_eval i (Div lhs rhs) (e1 / e2)" using assms by auto
  ultimately have "rel_err p i (Div lhs rhs) ((e1*(1 + r1) / (e2*(1 + r2)) - (e1/e2)) / (e1/e2))"
    using assms rel_err.simps by metis
  thus ?thesis using assms by simp
qed

lemma rel_err_prop_neg_template:
  assumes "exact_eval i ex e" and "rel_err p i ex r"
    and "(-(e * (1 + r)) - (-e)) / (-e) = res"
  shows "rel_err p i (Neg ex) res"
proof -
  have "rnd_eval p i (Neg ex) (-(e * (1 + r)))" using assms by blast
  moreover have "exact_eval i (Neg ex) (-e)" using assms by auto
  moreover have "e \<noteq> 0" using assms by blast
  ultimately have "rel_err p i (Neg ex) ((-(e * (1 + r)) - (-e)) / (-e))"
    using neg_equal_0_iff_equal rel_err.intros by metis 
  thus ?thesis using assms by simp
qed

lemma rel_err_prop_rnd_template:
  assumes "exact_eval i ex e" and "rel_err p i ex r"
    and "(e * (1 + r + p (e * (1 + r)) s / e) - e) / e = res"
  shows "rel_err p i (Rnd ex s) res"
proof -
  obtain f where f_def: "rnd_eval p i ex f" and f_eq: "f = e * (1 + r)" using assms by blast
  hence "rnd_eval p i (Rnd ex s) (f + p f s)" by blast
  moreover have "exact_eval i (Rnd ex s) e" using assms by blast
  moreover have "e \<noteq> 0" using assms by blast
  ultimately have "rel_err p i (Rnd ex s) ((f + p f s - e) / e)" by force
  hence "rel_err p i (Rnd ex s) ((e * (1 + r) + p (e * (1 + r)) s - e) / e)" using f_eq by simp
  moreover have "(e * (1 + r) + p (e * (1 + r)) s - e) / e
                = (e * (1 + r + p (e * (1 + r)) s / e) - e) / e"
    by (simp add: ring_class.ring_distribs(1))
  ultimately show ?thesis using assms by simp
qed

subsection \<open>Error propagation equations\<close>

subsubsection \<open>additive errors\<close>

lemma add_err_prop_add_eqn:
  "((e1::real) + a1) + (e2 + a2) - (e1 + e2) = a1 + a2"
  by linarith

lemma add_err_prop_mul_eqn:
  "((e1::real) + a1) * (e2 + a2) - (e1 * e2) = e1*a2 + a1*e2 + a1*a2"
  by algebra

lemma add_err_prop_div_eqn:
  assumes "(e2::real) \<noteq> 0" and "e2 + a2 \<noteq> 0"
  shows "(e1 + a1) / (e2 + a2) - (e1 / e2) = (a1*e2 - e1*a2) / (e2 * (e2 + a2))"
proof -
  have "(e1 + a1) / (e2 + a2) = (e2*(e1 + a1)) / (e2*(e2 + a2))" using assms by simp
  moreover have "e1 / e2 = (e1 * (e2 + a2)) / (e2 * (e2 + a2))" using assms by simp
  ultimately show ?thesis using assms by argo
qed

(*
lemma add_err_prop_neg_eqn:
  "-((e::real) + a) - (-e) = -a"
  by simp
*)

(*
lemma add_err_prop_rnd_eqn:
  "(e + a + (p :: real \<Rightarrow> 's \<Rightarrow> real) (e + a) s) - e = a + p (e + a) s"
  by simp
*)

subsubsection \<open>relative errors\<close>

lemma rel_err_prop_add_eqn:
  assumes "e1 + e2 \<noteq> 0"
  shows "(((e1::real) * (1 + r1)) + (e2 * (1 + r2)) - (e1 + e2)) / (e1 + e2)
        = (e1 / (e1 + e2)) * r1 + (e2 / (e1 + e2)) * r2"
  using assms by algebra

lemma rel_err_prop_mul_eqn:
  assumes "e1 * e2 \<noteq> 0"
  shows "((e1::real) * (1 + r1) * e2 * (1 + r2) - (e1 * e2)) / (e1 * e2) = r1 + r2 + r1*r2"
proof -
  have "(e1 * (1 + r1) * e2 * (1 + r2) - e1 * e2) / (e1 * e2)
                 = (e1*e2*r1 + e1*e2*r2 + e1*e2*r1*r2) / (e1 * e2)"
    by algebra
  also have "... = (e1*e2)*(r1 + r2 + r1*r2) / (e1 * e2)" by algebra
  also have "... = r1 + r2 + r1*r2" using assms by simp
  finally show ?thesis .
qed

lemma rel_err_prop_div_eqn:
  assumes "(e2::real) \<noteq> 0" and "e2 * (1 + r2) \<noteq> 0"
    and "e1 / e2 \<noteq> 0"
  shows "((e1 * (1 + r1)) / (e2 * (1 + r2)) - (e1 / e2)) / (e1 / e2) = (r1 - r2) / (1 + r2)"
proof -
  have "((e1 * (1 + r1)) / (e2 * (1 + r2)) - (e1 / e2)) / (e1 / e2)
                 = ((e1 + e1*r1) / (e2 + e2*r2) - e1 / e2) / (e1 / e2)" by algebra
  also have "... = ((e1 + e1*r1) / (e2 + e2*r2) - (e1 * (1 + r2)) / (e2 * (1 + r2))) / (e1 / e2)"
    using assms by simp
  also have "... = ((e1 + e1*r1 - (e1 + e1*r2)) / (e2 + e2*r2)) / (e1 / e2)" by algebra
  also have "... = e2*(e1 + e1*r1 - (e1 + e1*r2)) / (e1*e2*(1 + r2))" by argo
  also have "... = (e1*r1 - e1*r2) / (e1*(1 + r2))" using assms by simp
  also have "... = e1*(r1 - r2) / (e1*(1 + r2))" by algebra
  also have "... = (r1 - r2) / (1 + r2)" using assms by simp
  finally show ?thesis .
qed

lemma rel_err_prop_neg_eqn:
  assumes "-e \<noteq> 0"
  shows "(-((e::real) * (1 + r)) - (-e)) / (-e) = r"
  using assms by (simp add: diff_divide_distrib)

lemma rel_err_prop_rnd_eqn:
  fixes p :: "real \<Rightarrow> 's \<Rightarrow> real"
  assumes "e \<noteq> 0"
  shows "(e * (1 + r + p (e * (1 + r)) s / e) - e) / e = r + p (e * (1 + r)) s / e"
  using assms by (simp add: diff_divide_distrib)

text \<open>no equations for constants and variables, they always have zero error\<close>

subsection \<open>Final error propagation lemmas\<close>

(* TODO: these are probably not necessary. *)

subsubsection \<open>additive errors\<close>

lemma add_err_prop_add:
  assumes "add_err p i lhs a1" and "add_err p i rhs a2"
  shows "add_err p i (Add lhs rhs) (a1 + a2)"
  using add_errE add_err_prop_add_eqn add_err_prop_add_template assms by metis

lemma add_err_prop_mul:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "add_err p i lhs a1" and "add_err p i rhs a2"
  shows "add_err p i (Mul lhs rhs) (e1*a2 + a1*e2 + a1*a2)"
  using add_err_prop_mul_eqn add_err_prop_mul_template assms by metis

lemma add_err_prop_div:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "add_err p i lhs a1" and "add_err p i rhs a2"
    and "e2 \<noteq> 0" and "e2 + a2 \<noteq> 0"
  shows "add_err p i (Div lhs rhs) ((a1*e2 - e1*a2) / (e2 * (e2 + a2)))"
  using add_err_prop_div_eqn add_err_prop_div_template assms by metis

lemma add_err_prop_neg:
  assumes "add_err p i ex a"
  shows "add_err p i (Neg ex) (-a)"
  using assms using add_err.simps by fastforce

lemma add_err_prop_rnd:
  assumes "exact_eval i ex e" and "add_err p i ex a"
  shows "add_err p i (Rnd ex s) (a + p (e + a) s)"
  using assms by (simp add: add_err_prop_rnd_template)

lemma add_err_const:
  "add_err p i (Const c) 0"
  using add_err.simps by fastforce

lemma add_err_var:
  "add_err p i (Var x) 0"
  using add_err.simps by fastforce

subsubsection \<open>relative errors\<close>

lemma rel_err_prop_add:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "rel_err p i lhs r1" and "rel_err p i rhs r2"
    and "e1 + e2 \<noteq> 0"
  shows "rel_err p i (Add lhs rhs) ((e1 / (e1 + e2)) * r1 + (e2 / (e1 + e2)) * r2)"
  using rel_err_prop_add_eqn rel_err_prop_add_template assms by metis

lemma rel_err_prop_mul:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "rel_err p i lhs r1" and "rel_err p i rhs r2"
    and "e1 * e2 \<noteq> 0"
  shows "rel_err p i (Mul lhs rhs) (r1 + r2 + r1*r2)"
  using rel_err_prop_mul_eqn rel_err_prop_mul_template assms by metis

lemma rel_err_prop_div:
  assumes "exact_eval i lhs e1" and "exact_eval i rhs e2"
    and "rel_err p i lhs r1" and "rel_err p i rhs r2"
    and "e1 / e2 \<noteq> 0" and "e2 \<noteq> 0" and "e2 * (1 + r2) \<noteq> 0"
  shows "rel_err p i (Div lhs rhs) ((r1 - r2) / (1 + r2))"
  using rel_err_prop_div_eqn rel_err_prop_div_template assms by metis

lemma rel_err_prop_neg:
  assumes "exact_eval i ex e" and "rel_err p i ex a"
    and "-e \<noteq> 0"
  shows "rel_err p i (Neg ex) a"
  using rel_err_prop_neg_eqn rel_err_prop_neg_template assms by metis

lemma rel_err_prop_rnd:
  assumes "exact_eval i ex e" and "rel_err p i ex r"
    and "e \<noteq> 0"
  shows "rel_err p i (Rnd ex s) (r + p (e * (1 + r)) s / e)"
  using rel_err_prop_rnd_eqn rel_err_prop_rnd_template assms by metis

lemma rel_err_const:
  "exact_eval i (Const c) e \<Longrightarrow> e \<noteq> 0 \<Longrightarrow> rel_err p i (Const c) 0"
  using rel_err.simps by fastforce

lemma rel_err_var:
  "exact_eval i (Var x) e \<Longrightarrow> e \<noteq> 0 \<Longrightarrow> rel_err p i (Var x) 0"
  using rel_err.simps by fastforce

section \<open>Interval Arithmetic Definition\<close>

text \<open>We use level 1 natural interval extensions of set-flavored IEEE-1788 interval arithmetic.\<close>

definition set_add :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"set_add X Y = {x + y | x y. x \<in> X \<and> y \<in> Y}"

definition set_sub :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"set_sub X Y = {x - y | x y. x \<in> X \<and> y \<in> Y}"

definition set_mul :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"set_mul X Y = {x * y | x y. x \<in> X \<and> y \<in> Y}"

definition set_div :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"set_div X Y = {x / y | x y. x \<in> X \<and> y \<in> Y \<and> y \<noteq> 0}"

definition set_neg :: "real set \<Rightarrow> real set" where
"set_neg X = {-x | x. x \<in> X}"

definition ia_add :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"ia_add X Y = convex hull set_add X Y"

definition ia_sub :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"ia_sub X Y = convex hull set_sub X Y"

definition ia_mul :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"ia_mul X Y = convex hull set_mul X Y"

definition ia_div :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"ia_div X Y = convex hull set_div X Y"

definition ia_neg :: "real set \<Rightarrow> real set" where
"ia_neg X = convex hull set_neg X"

(* no convex hull needed if the inputs are intervals *)
definition ia_intersect :: "real set \<Rightarrow> real set \<Rightarrow> real set" where
"ia_intersect lhs rhs = convex hull (lhs \<inter> rhs)"

lemma ia_add_inc[simp]: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x + y \<in> ia_add X Y"
  using hull_inc[of "x + y" "set_add X Y" convex] ia_add_def set_add_def by auto

lemma ia_sub_inc[simp]: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x - y \<in> ia_sub X Y"
  using hull_inc[of "x - y" "set_sub X Y" convex] ia_sub_def set_sub_def by auto

lemma ia_mul_inc[simp]: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x * y \<in> ia_mul X Y"
  using hull_inc[of "x * y" "set_mul X Y" convex] ia_mul_def set_mul_def by auto

lemma ia_div_inc[simp]: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x / y \<in> ia_div X Y"
  using hull_inc[of "x / y" "set_div X Y" convex] ia_div_def set_div_def by auto

lemma ia_neg_inc[simp]: "x \<in> X \<Longrightarrow> -x  \<in> ia_neg X"
  using hull_inc[of "-x" "set_neg X" convex] ia_neg_def set_neg_def by auto

lemma "Y \<noteq> {} \<Longrightarrow> ia_add UNIV Y = UNIV" 
proof
  show "ia_add UNIV Y \<subseteq> UNIV" by simp
next
  show "Y \<noteq> {} \<Longrightarrow> UNIV \<subseteq> ia_add UNIV Y"
  proof
    assume "Y \<noteq> {}"
    then obtain y where y_def: "y \<in> Y" by blast
    fix z :: real
    have "z = (z - y) + y" by simp
    thus "z \<in> ia_add UNIV Y" unfolding ia_add_def set_add_def using hull_subset y_def by fast
  qed
qed

lemma "Y \<noteq> {} \<Longrightarrow> ia_sub UNIV Y = UNIV" 
proof
  show "ia_sub UNIV Y \<subseteq> UNIV" by simp
next
  show "Y \<noteq> {} \<Longrightarrow> UNIV \<subseteq> ia_sub UNIV Y"
  proof
    assume "Y \<noteq> {}"
    then obtain y where y_def: "y \<in> Y" by blast
    fix z :: real
    have "z = (z + y) - y" by simp
    thus "z \<in> ia_sub UNIV Y" unfolding ia_sub_def set_sub_def using hull_subset y_def by fast
  qed
qed

(*
lemma "Y \<noteq> {} \<Longrightarrow> ia_mul UNIV Y = UNIV"
proof
  show "ia_mul UNIV Y \<subseteq> UNIV" by simp
next
  show "Y \<noteq> {} \<Longrightarrow> UNIV \<subseteq> ia_mul UNIV Y"
  proof
    assume "Y \<noteq> {}"
    then obtain y where y_def: "y \<in> Y" by blast
    fix z :: real
    have "z = (z / y) * y" sorry (* false if y = 0 *)
    thus "z \<in> ia_mul UNIV Y" unfolding ia_mul_def set_mul_def using hull_subset y_def by fast
  qed
qed
*)

notation ia_add (infixl "+\<^sub>I" 65)
notation ia_sub (infixl "-\<^sub>I" 65)
notation ia_mul (infixl "*\<^sub>I" 70)
notation ia_div (infixl "\<div>\<^sub>I" 70)
notation ia_neg ("-\<^sub>I _" [81] 80)

section \<open>Basic Interval Functions\<close>

fun E :: "(nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set" where
"E I (Add lhs rhs) = E I lhs +\<^sub>I E I rhs" |
"E I (Mul lhs rhs) = E I lhs *\<^sub>I E I rhs" |
"E I (Div lhs rhs) = E I lhs \<div>\<^sub>I E I rhs" |
"E I (Neg ex) = -\<^sub>IE I ex" |
"E I (Rnd ex s) = E I ex" |
"E I (Const c) = {c}" |
"E I (Var x) = I x"

fun F :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set" where
"F P I (Add lhs rhs) = F P I lhs +\<^sub>I F P I rhs" |
"F P I (Mul lhs rhs) = F P I lhs *\<^sub>I F P I rhs" |
"F P I (Div lhs rhs) = F P I lhs \<div>\<^sub>I F P I rhs" |
"F P I (Neg ex) = -\<^sub>I F P I ex" |
"F P I (Rnd ex s) = F P I ex +\<^sub>I P (F P I ex) s" |
"F P I (Const c) = {c}" |
"F P I (Var x) = I x"

definition in_box :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> bool" where
"in_box i I \<longleftrightarrow> (\<forall> x. i x \<in> I x)"

definition is_perturbation_model :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> bool" where
"is_perturbation_model p P \<longleftrightarrow> (\<forall> x s X. x \<in> X \<longrightarrow> p x s \<in> P X s)"

theorem E_correct: "exact_eval i ex exact \<Longrightarrow> in_box i I \<Longrightarrow> exact \<in> E I ex"
  by (induction rule: exact_eval.induct) (simp_all add: in_box_def)

theorem F_correct: "rnd_eval p i ex rnd \<Longrightarrow> in_box i I \<Longrightarrow> is_perturbation_model p P \<Longrightarrow> rnd \<in> F P I ex"
  by (induction rule: rnd_eval.induct) (simp_all add: in_box_def is_perturbation_model_def)

subsection \<open>Basic additive error function and correctness proof\<close>

fun A :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set" where
"A P I (Add lhs rhs) = A P I lhs +\<^sub>I A P I rhs" |
"A P I (Mul lhs rhs) = E I lhs *\<^sub>I A P I rhs +\<^sub>I A P I lhs *\<^sub>I E I rhs +\<^sub>I A P I lhs *\<^sub>I A P I rhs" |
"A P I (Div lhs rhs) = (A P I lhs *\<^sub>I E I rhs -\<^sub>I E I lhs *\<^sub>I A P I rhs)
                       \<div>\<^sub>I (E I rhs *\<^sub>I (E I rhs +\<^sub>I A P I rhs))" |
"A P I (Neg ex) = -\<^sub>IA P I ex" |
"A P I (Rnd ex s) = A P I ex +\<^sub>I P (E I ex +\<^sub>I A P I ex) s" |
"A P I (Const c) = {0}" |
"A P I (Var x) = {0}"

theorem A_correct:
  assumes "add_err p i ex a" and "in_box i I" and "is_perturbation_model p P"
  shows "a \<in> A P I ex" using assms
proof (induction ex arbitrary: a)
  case (Add lhs rhs)
  from this obtain a1 a2 where
    a1_def: "add_err p i lhs a1" and a1_A: "a1 \<in> A P I lhs" and
    a2_def: "add_err p i rhs a2" and a2_A: "a2 \<in> A P I rhs" by blast
  hence "add_err p i (Add lhs rhs) (a1 + a2)" using add_err_prop_add by metis
  moreover have "a1 + a2 \<in> A P I (Add lhs rhs)" using a1_A a2_A by simp
  ultimately show ?case using Add add_err_unique by metis
next
  case (Mul lhs rhs)
  from this obtain a1 a2 where
    a1_def: "add_err p i lhs a1" and a1_A: "a1 \<in> A P I lhs" and
    a2_def: "add_err p i rhs a2" and a2_A: "a2 \<in> A P I rhs" by auto
  from this obtain e1 e2 where
    e1_def: "exact_eval i lhs e1" and
    e2_def: "exact_eval i rhs e2" by blast
  have e1_E: "e1 \<in> E I lhs" using E_correct e1_def assms by blast
  have e2_E: "e2 \<in> E I rhs" using E_correct e2_def assms by blast
  have "add_err p i (Mul lhs rhs) (e1*a2 + a1*e2 + a1*a2)"
    using add_err_prop_mul e1_def e2_def a1_def a2_def by metis
  moreover have "e1*a2 + a1*e2 + a1*a2 \<in> A P I (Mul lhs rhs)"
    using e1_def e2_def a1_def a2_def a1_A a2_A e1_E e2_E by simp
  ultimately show ?case using Mul add_err_unique by metis
next
  case (Div lhs rhs)
  from this obtain a1 a2 where
    a1_def: "add_err p i lhs a1" and a1_A: "a1 \<in> A P I lhs" and
    a2_def: "add_err p i rhs a2" and a2_A: "a2 \<in> A P I rhs" by auto
  from this obtain e1 e2 where
    e1_def: "exact_eval i lhs e1" and
    e2_def: "exact_eval i rhs e2" by blast
  have e1_E: "e1 \<in> E I lhs" using E_correct e1_def assms by blast
  have e2_E: "e2 \<in> E I rhs" using E_correct e2_def assms by blast
  have e2_neq_0: "e2 \<noteq> 0" using Div e2_def by blast
  have f2_neq_0: "e2 + a2 \<noteq> 0" using Div.prems(1) a2_def e2_def exact_eval_unique by fastforce
  have "add_err p i (Div lhs rhs) ((a1*e2 - e1*a2) / (e2 * (e2 + a2)))"
    using add_err_prop_div e1_def e2_def a1_def a2_def e2_neq_0 f2_neq_0 by metis
  moreover have "(a1*e2 - e1*a2) / (e2 * (e2 + a2)) \<in> A P I (Div lhs rhs)"
    using e1_def e2_def a1_def a2_def a1_A a2_A e1_E e2_E e2_neq_0 f2_neq_0 by simp
  ultimately show ?case using Div add_err_unique by metis
next
  case (Neg ex)
  from this obtain a1 where
    a1_def: "add_err p i ex a1" and a1_A: "a1 \<in> A P I ex" by blast
  have "add_err p i (Neg ex) (-a1)" using add_err_prop_neg a1_def by metis
  moreover have "-a1 \<in> A P I (Neg ex)" using a1_A by simp
  ultimately show ?case using Neg add_err_unique by metis
next
  case (Rnd ex s)
  from this obtain a1 where
    a1_def: "add_err p i ex a1" and a1_A: "a1 \<in> A P I ex" by blast
  from this obtain e1 where
    e1_def: "exact_eval i ex e1" by blast
  have e1_E: "e1 \<in> E I ex" using E_correct e1_def assms by blast
  have "add_err p i (Rnd ex s) (a1 + p (e1 + a1) s)"
    using add_err_prop_rnd e1_def a1_def by metis
  moreover have "a1 + p (e1 + a1) s \<in> A P I (Rnd ex s)"
    using a1_A e1_E assms unfolding is_perturbation_model_def by simp
  ultimately show ?case using Rnd add_err_unique by metis
qed auto

subsection \<open>Basic relative error function and correctness proof\<close>

fun R :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set" where
"R P I (Add lhs rhs) = (E I lhs \<div>\<^sub>I (E I lhs +\<^sub>I E I rhs)) *\<^sub>I R P I lhs
                       +\<^sub>I (E I rhs \<div>\<^sub>I (E I lhs +\<^sub>I E I rhs)) *\<^sub>I R P I rhs" |
"R P I (Mul lhs rhs) = R P I lhs +\<^sub>I R P I rhs +\<^sub>I R P I lhs *\<^sub>I R P I rhs" |
"R P I (Div lhs rhs) = (R P I lhs -\<^sub>I R P I rhs) \<div>\<^sub>I ({1} +\<^sub>I R P I rhs)" |
"R P I (Neg ex) = R P I ex" |
"R P I (Rnd ex s) = R P I ex +\<^sub>I P (E I ex *\<^sub>I ({1} +\<^sub>I R P I ex)) s" |
"R P I (Const c) = {0}" |
"R P I (Var x) = {0}"

text \<open>we can only propagate the relative error if it exists at each intermediate step\<close>

fun R_pre :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> bool" where
"R_pre p i (Add lhs rhs) \<longleftrightarrow>
  \<not>exact_eval i lhs 0 \<and> \<not>exact_eval i rhs 0 \<and> R_pre p i lhs \<and> R_pre p i rhs" |
"R_pre p i (Mul lhs rhs) \<longleftrightarrow>
  \<not>exact_eval i lhs 0 \<and> \<not>exact_eval i rhs 0 \<and> R_pre p i lhs \<and> R_pre p i rhs" |
"R_pre p i (Div lhs rhs) \<longleftrightarrow>
  \<not>exact_eval i lhs 0 \<and> \<not>exact_eval i rhs 0 \<and> R_pre p i lhs \<and> R_pre p i rhs" |
"R_pre p i (Neg ex) \<longleftrightarrow> \<not>exact_eval i ex 0 \<and> R_pre p i ex" |
"R_pre p i (Rnd ex s) \<longleftrightarrow> \<not>exact_eval i ex 0 \<and> R_pre p i ex" |
"R_pre p i (Const c) \<longleftrightarrow> c \<noteq> 0" |
"R_pre p i (Var x) \<longleftrightarrow> i x \<noteq> 0"

definition is_rel_perturbation_model :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> bool" where
"is_rel_perturbation_model p P \<longleftrightarrow> (\<forall> e r s X. e*(1 + r) \<in> X \<and> e \<noteq> 0 \<longrightarrow> p (e*(1 + r)) s / e \<in> P X s)"

theorem R_correct:
  assumes "rel_err p i ex r" and "in_box i I" and "is_rel_perturbation_model p P"
    and "R_pre p i ex"
  shows "r \<in> R P I ex" using assms
proof (induction ex arbitrary: r)
  case (Add lhs rhs)
  obtain r1 r2 where
    r1_def: "rel_err p i lhs r1" and r1_R: "r1 \<in> R P I lhs" and
    r2_def: "rel_err p i rhs r2" and r2_R: "r2 \<in> R P I rhs"
    using Add by auto
  obtain e1 e2 where
    e1_def: "exact_eval i lhs e1" and
    e2_def: "exact_eval i rhs e2"
    using r1_def r2_def by auto
  have e1_E: "e1 \<in> E I lhs" using E_correct e1_def assms by blast
  have e2_E: "e2 \<in> E I rhs" using E_correct e2_def assms by blast
  have res_neq_0: "e1 + e2 \<noteq> 0" using Add e1_def e2_def by blast
  have "rel_err p i (Add lhs rhs) ((e1 / (e1 + e2)) * r1 + (e2 / (e1 + e2)) * r2)"
    using rel_err_prop_add e1_def e2_def r1_def r2_def res_neq_0 by metis
  moreover have "(e1 / (e1 + e2)) * r1 + (e2 / (e1 + e2)) * r2 \<in> R P I (Add lhs rhs)"
    using r1_R r2_R e1_E e2_E res_neq_0 by (simp del: times_divide_eq_left)
  ultimately show ?case using Add rel_err_unique by metis
next
  case (Mul lhs rhs)
  obtain r1 r2 where
    r1_def: "rel_err p i lhs r1" and r1_R: "r1 \<in> R P I lhs" and
    r2_def: "rel_err p i rhs r2" and r2_R: "r2 \<in> R P I rhs"
    using Mul by auto
  obtain e1 e2 where
    e1_def: "exact_eval i lhs e1" and
    e2_def: "exact_eval i rhs e2"
    using r1_def r2_def by auto
  have res_neq_0: "e1 * e2 \<noteq> 0" using Mul e1_def e2_def by blast
  have "rel_err p i (Mul lhs rhs) (r1 + r2 + r1*r2)"
    using rel_err_prop_mul e1_def e2_def r1_def r2_def res_neq_0 by metis
  moreover have "r1 + r2 + r1*r2 \<in> R P I (Mul lhs rhs)"
    using r1_R r2_R by simp
  ultimately show ?case using Mul rel_err_unique by metis
next
  case (Div lhs rhs)
  obtain r1 r2 where
    r1_def: "rel_err p i lhs r1" and r1_R: "r1 \<in> R P I lhs" and
    r2_def: "rel_err p i rhs r2" and r2_R: "r2 \<in> R P I rhs"
    using Div by auto
  obtain e1 e2 where
    e1_def: "exact_eval i lhs e1" and
    e2_def: "exact_eval i rhs e2"
    using r1_def r2_def by auto
  have res_neq_0: "e1 / e2 \<noteq> 0" using Div e1_def e2_def by blast
  have e2_neq_0: "e2 \<noteq> 0" using e2_def Div by blast
  have f2_neq_0: "e2*(1 + r2) \<noteq> 0" using r2_def e2_def Div by blast
  have r2_neq_m1: "r2 \<noteq> -1" using e2_neq_0 f2_neq_0 by simp
  have "rel_err p i (Div lhs rhs) ((r1 - r2) / (1 + r2))"
    using rel_err_prop_div e1_def e2_def r1_def r2_def res_neq_0 e2_neq_0 f2_neq_0 by metis
  moreover have "(r1 - r2) / (1 + r2) \<in> R P I (Div lhs rhs)"
    using r1_R r2_R r2_neq_m1 by simp
  ultimately show ?case using Div rel_err_unique by metis
next
  case (Neg ex)
  obtain r1 where
    r1_def: "rel_err p i ex r1" and r1_R: "r1 \<in> R P I ex"
    using Neg by auto
  obtain e1 where
    e1_def: "exact_eval i ex e1"
    using r1_def by blast
  hence "-e1 \<noteq> 0" using Neg by auto
  hence "rel_err p i (Neg ex) r1" using rel_err_prop_neg e1_def r1_def by metis
  moreover have "r1 \<in> R P I (Neg ex)" using r1_R by simp
  ultimately show ?case using Neg rel_err_unique by metis
next
  case (Rnd ex s)
  from this obtain r1 where
    r1_def: "rel_err p i ex r1" and r1_R: "r1 \<in> R P I ex" by auto
  from this obtain e1 where
    e1_def: "exact_eval i ex e1" by blast
  have e1_E: "e1 \<in> E I ex" using E_correct e1_def assms by blast
  have e1_neq_0: "e1 \<noteq> 0" using Rnd e1_def by auto
  have "rel_err p i (Rnd ex s) (r1 + p (e1 * (1 + r1)) s / e1)"
    using rel_err_prop_rnd e1_def r1_def e1_neq_0 by metis
  moreover have "r1 + p (e1 * (1 + r1)) s / e1 \<in> R P I (Rnd ex s)"
    using r1_R e1_E assms e1_neq_0 unfolding is_rel_perturbation_model_def by simp
  ultimately show ?case using Rnd rel_err_unique by metis
qed auto

subsection \<open>Unified error function\<close>

fun RU0_ok :: "(nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> bool" where
"RU0_ok I (Add lhs rhs) \<longleftrightarrow> 0 \<notin> E I (Add lhs rhs) \<and> 0 \<notin> E I lhs \<and> 0 \<notin> E I rhs" |
"RU0_ok I (Mul lhs rhs) \<longleftrightarrow> 0 \<notin> E I (Mul lhs rhs) \<and> 0 \<notin> E I lhs \<and> 0 \<notin> E I rhs" |
"RU0_ok I (Div lhs rhs) \<longleftrightarrow> 0 \<notin> E I (Div lhs rhs) \<and> 0 \<notin> E I lhs \<and> 0 \<notin> E I rhs" |
"RU0_ok I (Neg ex) \<longleftrightarrow> 0 \<notin> E I ex" |
"RU0_ok I (Rnd ex s) \<longleftrightarrow> 0 \<notin> E I ex" |
"RU0_ok I (Const c) \<longleftrightarrow> c \<noteq> 0" |
"RU0_ok I (Var x) \<longleftrightarrow> 0 \<notin> I x"

fun AU :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set"
and RU :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set"
and AU0 :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set"
and RU0 :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set" where
"AU P S I ex = (if RU0_ok I ex then ia_intersect (AU0 P S I ex) (RU0 P S I ex *\<^sub>I E I ex) else AU0 P S I ex)" |
"RU P S I ex = (if RU0_ok I ex then ia_intersect (RU0 P S I ex) (AU0 P S I ex \<div>\<^sub>I E I ex) else AU0 P S I ex \<div>\<^sub>I E I ex)" |
"AU0 P S I (Add lhs rhs) = AU P S I lhs +\<^sub>I AU P S I rhs" |
"AU0 P S I (Mul lhs rhs) = E I lhs *\<^sub>I AU P S I rhs +\<^sub>I AU P S I lhs *\<^sub>I E I rhs +\<^sub>I AU P S I lhs *\<^sub>I AU P S I rhs" |
"AU0 P S I (Div lhs rhs) = (AU P S I lhs *\<^sub>I E I rhs -\<^sub>I E I lhs *\<^sub>I AU P S I rhs)
                           \<div>\<^sub>I (E I rhs *\<^sub>I (E I rhs +\<^sub>I AU P S I rhs))" |
"AU0 P S I (Neg ex) = -\<^sub>IAU P S I ex" |
"AU0 P S I (Rnd ex s) = AU P S I ex +\<^sub>I P (E I ex +\<^sub>I AU P S I ex) s" |
"AU0 P S I (Const c) = {0}" |
"AU0 P S I (Var x) = {0}" |
"RU0 P S I (Add lhs rhs) = (E I lhs \<div>\<^sub>I (E I lhs +\<^sub>I E I rhs)) *\<^sub>I RU P S I lhs
                           +\<^sub>I (E I rhs \<div>\<^sub>I (E I lhs +\<^sub>I E I rhs)) *\<^sub>I RU P S I rhs" |
"RU0 P S I (Mul lhs rhs) = RU P S I lhs +\<^sub>I RU P S I rhs +\<^sub>I RU P S I lhs *\<^sub>I RU P S I rhs" |
"RU0 P S I (Div lhs rhs) = (RU P S I lhs -\<^sub>I RU P S I rhs) \<div>\<^sub>I ({1} +\<^sub>I RU P S I rhs)" |
"RU0 P S I (Neg ex) = RU P S I ex" |
"RU0 P S I (Rnd ex s) = RU P S I ex +\<^sub>I P (E I ex *\<^sub>I ({1} +\<^sub>I RU P S I ex)) s" |
"RU0 P S I (Const c) = {0}" |
"RU0 P S I (Var x) = {0}"

lemma ia_intersect_inc [dest]: "x \<in> X \<Longrightarrow> x \<in> Y \<Longrightarrow> x \<in> ia_intersect X Y"
  unfolding ia_intersect_def by (simp add: hull_inc)

theorem AU_RU_correct:
  assumes "in_box i I" and "is_perturbation_model p P" and "is_rel_perturbation_model p S"
  shows "\<And> a. add_err p i ex a \<Longrightarrow> a \<in> AU P S I ex"
   and  "\<And> r. rel_err p i ex r \<Longrightarrow> r \<in> RU P S I ex"
   and  "\<And> a. add_err p i ex a \<Longrightarrow> a \<in> AU0 P S I ex"
   and  "\<And> r. rel_err p i ex r \<Longrightarrow> RU0_ok I ex \<Longrightarrow> r \<in> RU0 P S I ex"
  using assms
proof (induction P S I ex and P S I ex and P S I ex and P S I ex rule: AU_RU_AU0_RU0.induct)
  case (1 P S I ex)
  from this obtain e where e_def: "exact_eval i ex e" by blast
  show ?case
  proof (cases "RU0_ok I ex")
    case True
    hence a_in: "a \<in> AU0 P S I ex" using 1 by blast
    have E_not_0: "0 \<notin> E I ex" sorry
    obtain e where e_def: "exact_eval i ex e" using 1 by blast
    have e_neq_0: "e \<noteq> 0" using e_def E_correct E_not_0 1 by metis
    obtain r where r_def: "rel_err p i ex r" using e_neq_0 e_def 1 by blast
    have r_in: "r \<in> RU0 P S I ex" using r_def 1 True by simp 
    hence "a = r * e" using add_from_rel_err e_def r_def add_err_unique 1 by metis
    hence "a \<in> RU0 P S I ex *\<^sub>I E I ex" using r_in e_def 1 E_correct ia_mul_inc by metis
    thus ?thesis using a_in ia_intersect_inc by simp
  next
    case False
    thus ?thesis using 1 by simp
  qed
next
  case (2 P S I ex)
  then show ?case sorry
next
  case (3 P S I lhs rhs)
  then show ?case sorry
next
  case (4 P S I lhs rhs)
  then show ?case sorry
next
  case (5 P S I lhs rhs)
  then show ?case sorry
next
  case (6 P S I ex)
  then show ?case sorry
next
  case (7 P S I ex s)
  then show ?case sorry
next
  case (8 P S I c)
  then show ?case sorry
next
  case (9 P S I x)
  then show ?case sorry
next
  case (10 P S I lhs rhs)
  then show ?case sorry
next
  case (11 P S I lhs rhs)
  then show ?case sorry
next
  case (12 P S I lhs rhs)
  then show ?case sorry
next
  case (13 P S I ex)
  then show ?case sorry
next
  case (14 P S I ex s)
  then show ?case sorry
next
  case (15 P S I c)
  then show ?case sorry
next
  case (16 P S I x)
  then show ?case sorry
qed


end