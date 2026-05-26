theory RoundingErrors2
imports Complex_Main "HOL-Analysis.Convex"
begin

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

lemma ia_intersect_inc: "x \<in> X \<Longrightarrow> x \<in> Y \<Longrightarrow> x \<in> ia_intersect X Y"
  unfolding ia_intersect_def by (simp add: hull_inc)

notation ia_add (infixl "+\<^sub>I" 65)
notation ia_sub (infixl "-\<^sub>I" 65)
notation ia_mul (infixl "*\<^sub>I" 70)
notation ia_div (infixl "\<div>\<^sub>I" 70)
notation ia_neg ("-\<^sub>I _" [81] 80)

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

definition ia_p_model :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> bool" where
"ia_p_model p P \<longleftrightarrow> (\<forall> x s X. x \<in> X \<longrightarrow> p x s \<in> P X s)"

definition ia_s_model :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> bool" where
"ia_s_model p S \<longleftrightarrow> (\<forall> e f s F. f \<in> F \<and> e \<noteq> 0 \<longrightarrow> p f s / e \<in> S F s)"

definition in_box :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> bool" where
"in_box i I \<longleftrightarrow> (\<forall> x. i x \<in> I x)"

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

fun A :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set" where
"A P I (Add lhs rhs) = A P I lhs +\<^sub>I A P I rhs" |
"A P I (Mul lhs rhs) = A P I lhs *\<^sub>I E I rhs +\<^sub>I E I lhs *\<^sub>I A P I rhs + A P I lhs *\<^sub>I A P I rhs" |
"A P I (Div lhs rhs) = (A P I lhs *\<^sub>I E I rhs -\<^sub>I E I lhs *\<^sub>I A P I rhs)
                       \<div>\<^sub>I (E I rhs *\<^sub>I (E I rhs +\<^sub>I A P I rhs))" |
"A P I (Neg ex) = -\<^sub>IA P I ex" |
"A P I (Rnd ex s) = A P I ex +\<^sub>I P (E I ex +\<^sub>I A P I ex) s" |
"A P I (Const c) = {0}" |
"A P I (Var x) = {0}"

fun R_pre :: "(nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> bool" where
"R_pre I (Add lhs rhs) \<longleftrightarrow> 0 \<notin> E I lhs \<and> 0 \<notin> E I rhs \<and> R_pre I lhs \<and> R_pre I rhs" |
"R_pre I (Mul lhs rhs) \<longleftrightarrow> 0 \<notin> E I lhs \<and> 0 \<notin> E I rhs \<and> R_pre I lhs \<and> R_pre I rhs" |
"R_pre I (Div lhs rhs) \<longleftrightarrow> 0 \<notin> E I lhs \<and> 0 \<notin> E I rhs \<and> R_pre I lhs \<and> R_pre I rhs" |
"R_pre I (Neg ex) \<longleftrightarrow> 0 \<notin> E I ex \<and> R_pre I ex" |
"R_pre I (Rnd ex s) \<longleftrightarrow> 0 \<notin> E I ex \<and> R_pre I ex" |
"R_pre I (Const c) \<longleftrightarrow> True" |
"R_pre I (Var x) \<longleftrightarrow> True"

fun R :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set" where
"R S I (Add lhs rhs) = (E I lhs \<div>\<^sub>I (E I lhs +\<^sub>I E I rhs)) *\<^sub>I R S I lhs
                       +\<^sub>I (E I rhs \<div>\<^sub>I (E I lhs +\<^sub>I E I rhs)) *\<^sub>I R S I rhs" |
"R S I (Mul lhs rhs) = R S I lhs +\<^sub>I R S I rhs +\<^sub>I R S I lhs *\<^sub>I R S I rhs" |
"R S I (Div lhs rhs) = (R S I lhs -\<^sub>I R S I rhs) \<div>\<^sub>I ({1} +\<^sub>I R S I rhs)" |
"R S I (Neg ex) = R S I ex" |
"R S I (Rnd ex s) = R S I ex +\<^sub>I S (E I ex *\<^sub>I ({1} +\<^sub>I R S I ex)) s" |
"R S I (Const c) = {0}" |
"R S I (Var x) = {0}"

fun RU0_ok :: "(nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> bool" where
"RU0_ok I (Add lhs rhs) \<longleftrightarrow> 0 \<notin> E I (Add lhs rhs) \<and> 0 \<notin> E I lhs \<and> 0 \<notin> E I rhs" |
"RU0_ok I (Mul lhs rhs) \<longleftrightarrow> 0 \<notin> E I (Mul lhs rhs) \<and> 0 \<notin> E I lhs \<and> 0 \<notin> E I rhs" |
"RU0_ok I (Div lhs rhs) \<longleftrightarrow> 0 \<notin> E I (Div lhs rhs) \<and> 0 \<notin> E I lhs \<and> 0 \<notin> E I rhs" |
"RU0_ok I (Neg ex) \<longleftrightarrow> 0 \<notin> E I (Neg ex) \<and> 0 \<notin> E I ex" |
"RU0_ok I (Rnd ex s) \<longleftrightarrow> 0 \<notin> E I (Rnd ex s) \<and> 0 \<notin> E I ex" |
"RU0_ok I (Const c) \<longleftrightarrow> c \<noteq> 0" |
"RU0_ok I (Var x) \<longleftrightarrow> 0 \<notin> I x"

fun AU :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set"
and RU :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set"
and AU0 :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set"
and RU0 :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set" where
"AU P S I ex = (if RU0_ok I ex then ia_intersect (AU0 P S I ex) (RU0 P S I ex *\<^sub>I E I ex) else AU0 P S I ex)" |
"RU P S I ex = (if RU0_ok I ex then ia_intersect (RU0 P S I ex) (AU0 P S I ex \<div>\<^sub>I E I ex) else AU0 P S I ex \<div>\<^sub>I E I ex)" |
"AU0 P S I (Add lhs rhs) = AU P S I lhs +\<^sub>I AU P S I rhs" |
"AU0 P S I (Mul lhs rhs) = AU P S I lhs *\<^sub>I E I rhs +\<^sub>I E I lhs *\<^sub>I AU P S I rhs + AU P S I lhs *\<^sub>I AU P S I rhs" |
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
"RU0 P S I (Rnd ex s) = RU P S I ex +\<^sub>I S (E I ex *\<^sub>I ({1} +\<^sub>I RU P S I ex)) s" |
"RU0 P S I (Const c) = {0}" |
"RU0 P S I (Var x) = {0}"

(*fun A_hat :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set \<Rightarrow> real set" where
"A_hat P I (Add lhs rhs) acc = A_hat P I lhs (acc * A_bar P I (Add lhs rhs) lhs)
                               +\<^sub>I A_hat P I rhs (acc * A_bar P I (Add lhs rhs) rhs)" |
"A_hat P I (Mul lhs rhs) acc = A_hat P I lhs (acc * A_bar P I (Mul lhs rhs) lhs)
                               +\<^sub>I A_hat P I rhs (acc * A_bar P I (Mul lhs rhs) rhs)" |
"A_hat P I (Div lhs rhs) acc = A_hat P I lhs (acc * A_bar P I (Div lhs rhs) lhs)
                               +\<^sub>I A_hat P I rhs (acc * A_bar P I (Div lhs rhs) rhs)" |
"A_hat P I (Neg ex) sub = (if sub = ex then -\<^sub>IA P I ex else {0})" |
"A_hat P I (Rnd ex s) sub = (if sub = ex then A P I ex else {0})" |
"A_hat P I (Const c) ex = {0}" |
"A_hat P I (Var x) ex = {0}"*)

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

lemma exact_eval_unique [dest]: "exact_eval i ex e1 \<Longrightarrow> exact_eval i ex e2 \<Longrightarrow> e1 = e2"
  by (induction ex arbitrary: e1 e2) auto

lemma rnd_eval_unique [dest]: "rnd_eval p i ex e1 \<Longrightarrow> rnd_eval p i ex e2 \<Longrightarrow> e1 = e2"
  by (induction ex arbitrary: e1 e2) auto

lemma add_err_unique [dest]: "add_err p i ex a1 \<Longrightarrow> add_err p i ex a2 \<Longrightarrow> a1 = a2"
  by blast

lemma rel_err_unique [dest]: "rel_err p i ex r1 \<Longrightarrow> rel_err p i ex r2 \<Longrightarrow> r1 = r2"
  by blast

lemma rel_from_add_err:
  "exact_eval i ex e \<Longrightarrow> add_err p i ex a \<Longrightarrow> e \<noteq> 0 \<Longrightarrow> rel_err p i ex (a / e)"
  by blast

lemma rel_from_add_err_ia:
  assumes "a \<in> A1" and "add_err p i ex a"
      and "e \<in> E1" and "exact_eval i ex e"
      and "rel_err p i ex r"
    shows "r \<in> A1 \<div>\<^sub>I E1"
proof -
  have "e \<noteq> 0" using assms by blast
  hence "r = a / e" using rel_from_add_err assms by blast
  thus "r \<in> A1 \<div>\<^sub>I E1" using assms by force
qed

lemma add_from_rel_err:
  "exact_eval i ex e \<Longrightarrow> rel_err p i ex r \<Longrightarrow> add_err p i ex (r * e)"
  by force

lemma add_from_rel_err_ia:
  assumes "r \<in> R1" and "rel_err p i ex r"
      and "e \<in> E1" and "exact_eval i ex e"
      and "add_err p i ex a"
    shows "a \<in> R1 *\<^sub>I E1"
  using assms add_err_unique add_from_rel_err ia_mul_inc by metis

lemma add_exact_to_rnd:
  "add_err p i ex a \<Longrightarrow> exact_eval i ex e \<Longrightarrow> rnd_eval p i ex (e + a)" by auto

lemma add_exact_to_rnd_ia:
  assumes "a \<in> A1" and "add_err p i ex a"
      and "e \<in> E1" and "exact_eval i ex e"
      and "rnd_eval p i ex r"
    shows "r \<in> E1 +\<^sub>I A1"
  using assms add_exact_to_rnd ia_add_inc rnd_eval_unique by metis

lemma rel_exact_to_rnd:
  "rel_err p i ex r \<Longrightarrow> exact_eval i ex e \<Longrightarrow> rnd_eval p i ex (e * (1 + r))"
proof -
  fix r e
  assume r_def: "rel_err p i ex r" and e_def: "exact_eval i ex e"
  obtain f where f_def: "rnd_eval p i ex f" using r_def by auto
  have neq: "e \<noteq> 0" using r_def e_def by blast
  have "r = (f - e) / e" using r_def e_def f_def by blast
  hence "r*e = f - e" using neq by simp
  hence "f = e*(1 + r)" by algebra
  thus "rnd_eval p i ex (e*(1 + r))" using f_def by blast
qed

lemma rel_exact_to_rnd_ia:
  assumes "r \<in> R1" and "rel_err p i ex r"
      and "e \<in> E1" and "exact_eval i ex e"
      and "rnd_eval p i ex f"
    shows "f \<in> E1 *\<^sub>I ({1} +\<^sub>I R1)"
  using assms rel_exact_to_rnd ia_add_inc ia_mul_inc rnd_eval_unique singletonI[of 1] by metis

lemma add_add_prop1:
  assumes "add_err p i lhs a1" and "add_err p i rhs a2"
    shows "add_err p i (Add lhs rhs) (a1 + a2)"
proof -
  obtain e1 e2 r1 r2 where
    e1_def: "exact_eval i lhs e1" and e2_def: "exact_eval i rhs e2" and
    r1_def: "rnd_eval p i lhs r1" and r2_def: "rnd_eval p i rhs r2" and
    a1_def: "a1 = r1 - e1" and a2_def: "a2 = r2 - e2"
    using assms by auto
  have "exact_eval i (Add lhs rhs) (e1 + e2)" using e1_def e2_def by auto
  moreover have "rnd_eval p i (Add lhs rhs) (r1 + r2)" using r1_def r2_def by auto
  moreover have "(r1 + r2) - (e1 + e2) = a1 + a2" using a1_def a2_def by auto
  ultimately show "add_err p i (Add lhs rhs) (a1 + a2)" using add_err.intros by metis
qed

lemma add_add_prop1_ia:
  assumes "a1 \<in> A1" and "add_err p i lhs a1"
      and "a2 \<in> A2" and "add_err p i rhs a2"
      and "add_err p i (Add lhs rhs) a3"
    shows "a3 \<in> A1 +\<^sub>I A2"
  using assms add_add_prop1 add_err_unique ia_add_inc by metis

lemma add_mul_prop1:
  assumes "add_err p i lhs a1" and "add_err p i rhs a2"
      and "exact_eval i lhs e1" and "exact_eval i rhs e2"
    shows "add_err p i (Mul lhs rhs) (a1*e2 + e1*a2 + a1*a2)"
proof -
  obtain r1 r2 where
    r1_def: "rnd_eval p i lhs r1" and r2_def: "rnd_eval p i rhs r2" and
    a1_def: "a1 = r1 - e1" and a2_def: "a2 = r2 - e2"
    using assms by auto
  have "(r1 * r2) - (e1 * e2) = a1*e2 + e1*a2 + a1*a2" using a1_def a2_def by algebra
  moreover have "exact_eval i (Mul lhs rhs) (e1 * e2)" using assms by auto
  moreover have "rnd_eval p i (Mul lhs rhs) (r1 * r2)" using r1_def r2_def by auto
  ultimately show "add_err p i (Mul lhs rhs) (a1*e2 + e1*a2 + a1*a2)" using add_err.intros by metis
qed

lemma add_mul_prop1_ia:
  assumes "a1 \<in> A1" and "add_err p i lhs a1" and "e1 \<in> E1" and "exact_eval i lhs e1"
      and "a2 \<in> A2" and "add_err p i rhs a2" and "e2 \<in> E2" and "exact_eval i rhs e2"
      and "add_err p i (Mul lhs rhs) a3"
    shows "a3 \<in> A1*\<^sub>IE2 +\<^sub>I E1*\<^sub>IA2 + A1*\<^sub>IA2"
proof -
  have "a3 = a1*e2 + e1*a2 + a1*a2" using add_err_unique assms add_mul_prop1 by meson
  moreover have "a1*e2 + e1*a2 + a1*a2 \<in> A1*\<^sub>IE2 +\<^sub>I E1*\<^sub>IA2 + A1*\<^sub>IA2" using assms by force
  ultimately show ?thesis by simp
qed

lemma add_div_prop1:
  assumes "add_err p i lhs a1" and "add_err p i rhs a2"
      and "exact_eval i lhs e1" and "exact_eval i rhs e2"
      and "rnd_eval p i rhs r2" and "e2 \<noteq> 0" and "r2 \<noteq> 0"
    shows "add_err p i (Div lhs rhs) ((a1*e2 - e1*a2) / (e2 * r2))"
proof -
  obtain r1 where
    r1_def: "rnd_eval p i lhs r1" and
    a1_def: "a1 = r1 - e1" and a2_def: "a2 = r2 - e2"
    using assms by blast
  have "(r1 / r2) - (e1 / e2) = (a1*e2 - e1*a2) / (e2*r2)"
    using assms by (simp add: a1_def a2_def diff_frac_eq mult.commute right_diff_distrib')
  moreover have "exact_eval i (Div lhs rhs) (e1 / e2)" using assms by auto
  moreover have "rnd_eval p i (Div lhs rhs) (r1 / r2)" using r1_def assms by auto
  ultimately show "add_err p i (Div lhs rhs) ((a1*e2 - e1*a2) / (e2*r2))"
    using add_err.intros by metis
qed

lemma add_div_prop1_ia:
  assumes "a1 \<in> A1" and "add_err p i lhs a1" and "e1 \<in> E1" and "exact_eval i lhs e1"
      and "a2 \<in> A2" and "add_err p i rhs a2" and "e2 \<in> E2" and "e2 \<noteq> 0" and "exact_eval i rhs e2"
      and "r2 \<in> R2" and "r2 \<noteq> 0" and "rnd_eval p i rhs r2"
      and "add_err p i (Div lhs rhs) a3"
    shows "a3 \<in> (A1*\<^sub>IE2 -\<^sub>I E1*\<^sub>IA2) \<div>\<^sub>I (E2 *\<^sub>I R2)"
proof -
  have "a3 = (a1*e2 - e1*a2) / (e2 * r2)" using add_err_unique assms add_div_prop1 by meson
  moreover have "(a1*e2 - e1*a2) / (e2 * r2) \<in> (A1*\<^sub>IE2 -\<^sub>I E1*\<^sub>IA2) \<div>\<^sub>I (E2 *\<^sub>I R2)" using assms by force
  ultimately show ?thesis by simp
qed

lemma add_neg_prop1:
  assumes "add_err p i ex a"
    shows "add_err p i (Neg ex) (-a)"
  using assms add_err.simps by fastforce

lemma add_neg_prop1_ia:
  assumes "a1 \<in> A1" and "add_err p i ex a1"
      and "add_err p i (Neg ex) a2"
    shows "a2 \<in> -\<^sub>IA1"
  using assms add_neg_prop1 add_err_unique ia_neg_inc by metis

lemma add_rnd_prop1:
  assumes "add_err p i ex a" and "rnd_eval p i ex r"
    shows "add_err p i (Rnd ex s) (a + p r s)"
  using assms add_err.simps by fastforce

lemma add_rnd_prop1_ia:
  assumes "a1 \<in> A1" and "add_err p i ex a1"
      and "r1 \<in> R1" and "rnd_eval p i ex r1"
      and "add_err p i (Rnd ex s) a2"
      and "ia_p_model p P"
    shows "a2 \<in> A1 +\<^sub>I P R1 s"
proof -
  have "a2 = a1 + p r1 s" using assms add_rnd_prop1 add_err_unique by meson
  moreover have "a1 + p r1 s \<in> A1 +\<^sub>I P R1 s" using assms unfolding ia_p_model_def by auto
  ultimately show ?thesis by simp
qed

lemma rel_add_prop1:
  assumes "rel_err p i lhs r1" and "rel_err p i rhs r2"
      and "exact_eval i lhs e1" and "exact_eval i rhs e2"
      and "e1 + e2 \<noteq> 0"
    shows "rel_err p i (Add lhs rhs) (e1 / (e1 + e2) * r1 + e2 / (e1 + e2) * r2)"
proof -
  obtain f1 f2 where
    f1_def: "rnd_eval p i lhs f1" and r1_def: "r1 = (f1 - e1) / e1" and
    f2_def: "rnd_eval p i rhs f2" and r2_def: "r2 = (f2 - e2) / e2"
    using assms by auto
  have "(e1 / (e1 + e2) * r1 + e2 / (e1 + e2) * r2) = (f1 - e1) / (e1 + e2) + (f2 - e2) / (e1 + e2)"
    using r1_def r2_def assms by auto
  also have "... = ((f1 + f2) - (e1 + e2)) / (e1 + e2)" by algebra
  finally have "((f1 + f2) - (e1 + e2)) / (e1 + e2) = e1 / (e1 + e2) * r1 + e2 / (e1 + e2) * r2"
    by simp
  moreover have "exact_eval i (Add lhs rhs) (e1 + e2)" using assms by auto
  moreover have "rnd_eval p i (Add lhs rhs) (f1 + f2)" using f1_def f2_def by auto
  ultimately show ?thesis using rel_err.intros assms by metis
qed

lemma rel_add_prop1_ia:
  assumes "r1 \<in> R1" and "rel_err p i lhs r1" and "r2 \<in> R2" and "rel_err p i rhs r2"
      and "e1 \<in> E1" and "exact_eval i lhs e1" and "e2 \<in> E2" and "exact_eval i rhs e2"
      and "e1 + e2 \<noteq> 0"
      and "rel_err p i (Add lhs rhs) r3"
    shows "r3 \<in> (E1 \<div>\<^sub>I (E1 +\<^sub>I E2)) *\<^sub>I R1 +\<^sub>I (E2 \<div>\<^sub>I (E1 +\<^sub>I E2)) *\<^sub>I R2"
proof -
  have "r3 = (e1 / (e1 + e2) * r1 + e2 / (e1 + e2) * r2)"
    using assms rel_add_prop1 rel_err_unique by meson
  moreover have "(e1 / (e1 + e2) * r1 + e2 / (e1 + e2) * r2)
                  \<in> (E1 \<div>\<^sub>I (E1 +\<^sub>I E2)) *\<^sub>I R1 +\<^sub>I (E2 \<div>\<^sub>I (E1 +\<^sub>I E2)) *\<^sub>I R2"
    using assms ia_add_inc ia_div_inc ia_mul_inc by metis
  ultimately show ?thesis by simp
qed

lemma rel_mul_prop1:
  assumes "rel_err p i lhs r1" and "rel_err p i rhs r2"
      and "exact_eval i lhs e1" and "exact_eval i rhs e2"
      and "e1 * e2 \<noteq> 0"
    shows "rel_err p i (Mul lhs rhs) (r1 + r2 + r1*r2)"
proof -
  obtain f1 f2 where f1_def: "rnd_eval p i lhs f1" and f2_def: "rnd_eval p i rhs f2"
    using assms by blast
  have r1_def: "f1 = e1*(1 + r1)" using assms f1_def rel_exact_to_rnd rnd_eval_unique by meson
  have r2_def: "f2 = e2*(1 + r2)" using assms f2_def rel_exact_to_rnd rnd_eval_unique by meson
  have "f1*f2 - e1*e2 = e1*e2*(r1 + r2 + r1*r2)" using r1_def r2_def by algebra
  hence "(f1*f2 - e1*e2) / (e1*e2) = r1 + r2 + r1*r2" using assms by simp
  moreover have "exact_eval i (Mul lhs rhs) (e1 * e2)" using assms by auto
  moreover have "rnd_eval p i (Mul lhs rhs) (f1 * f2)" using f1_def f2_def by auto
  ultimately show ?thesis using rel_err.intros assms by metis
qed

lemma rel_mul_prop1_ia:
  assumes "r1 \<in> R1" and "rel_err p i lhs r1" and "r2 \<in> R2" and "rel_err p i rhs r2"
      and "e1 \<in> E1" and "exact_eval i lhs e1" and "e2 \<in> E2" and "exact_eval i rhs e2"
      and "e1 * e2 \<noteq> 0"
      and "rel_err p i (Mul lhs rhs) r3"
    shows "r3 \<in> R1 +\<^sub>I R2 +\<^sub>I R1*\<^sub>IR2" using assms
proof -
  have "r3 = r1 + r2 + r1*r2" using assms rel_mul_prop1 rel_err_unique by meson
  moreover have "r1 + r2 + r1*r2 \<in> R1 +\<^sub>I R2 +\<^sub>I R1*\<^sub>IR2" using assms by simp
  ultimately show ?thesis by simp
qed

lemma rel_div_prop1:
  assumes "rel_err p i lhs r1" and "rel_err p i rhs r2"
      and "exact_eval i lhs e1" and "exact_eval i rhs e2"
      and "rnd_eval p i rhs f2" and "f2 \<noteq> 0"
      and "e1 / e2 \<noteq> 0"
    shows "rel_err p i (Div lhs rhs) ((r1 - r2) / (1 + r2))"
proof -
  obtain f1 where f1_def: "rnd_eval p i lhs f1" using assms by blast
  have r1_def: "f1 = e1*(1 + r1)" using assms f1_def rel_exact_to_rnd rnd_eval_unique by meson
  have r2_def: "f2 = e2*(1 + r2)" using assms rel_exact_to_rnd rnd_eval_unique by meson
  have "r2 \<noteq> -1" using assms r2_def by algebra
  hence "e1 / e2 = (e1*(1 + r2)) / (e2*(1 + r2))" by simp
  hence "e1 / e2 = (e1 + e1*r2) / (e2 + e2*r2)" by argo
  moreover have "f1/f2 = (e1 + e1*r1) / (e2 + e2*r2)"
    using r1_def r2_def by (simp add: distrib_left)
  ultimately have "f1/f2 - e1/e2 = (e1/e2)*(r1 - r2) / (1 + r2)" by argo
  hence "(f1/f2 - e1/e2) / (e1/e2) = (r1 - r2) / (1 + r2)" using assms by simp
  moreover have "exact_eval i (Div lhs rhs) (e1 / e2)" using assms by auto
  moreover have "rnd_eval p i (Div lhs rhs) (f1 / f2)" using f1_def assms by auto
  ultimately show ?thesis using rel_err.intros assms by metis
qed

lemma rel_div_prop1_ia:
  assumes "r1 \<in> R1" and "rel_err p i lhs r1" and "r2 \<in> R2" and "rel_err p i rhs r2"
      and "e1 \<in> E1" and "exact_eval i lhs e1" and "e2 \<in> E2" and "exact_eval i rhs e2"
      and "f2 \<in> F2" and "rnd_eval p i rhs f2" and "f2 \<noteq> 0"
      and "e1 / e2 \<noteq> 0"
      and "rel_err p i (Div lhs rhs) r3"
    shows "r3 \<in> (R1 -\<^sub>I R2) \<div>\<^sub>I ({1} +\<^sub>I R2)"
proof -
  have neq: "1 + r2 \<noteq> 0" using assms mult_eq_0_iff rel_exact_to_rnd rnd_eval_unique by metis
  have "r3 = (r1 - r2) / (1 + r2)" using assms rel_div_prop1 rel_err_unique by meson
  moreover have "(r1 - r2) / (1 + r2) \<in> (R1 -\<^sub>I R2) \<div>\<^sub>I ({1} +\<^sub>I R2)" using assms neq by simp
  ultimately show ?thesis by simp
qed

lemma rel_neg_prop1:
  assumes "rel_err p i ex r"
      and "exact_eval i ex e"
    shows "rel_err p i (Neg ex) r"
proof -
  obtain f where f_def: "rnd_eval p i ex f" using assms by blast
  have "((-f) - (-e)) / (-e) = (f - e) / e" by argo
  hence "((-f) - (-e)) / (-e) = r" using assms f_def by auto
  moreover have "exact_eval i (Neg ex) (-e)" using assms by auto
  moreover have "rnd_eval p i (Neg ex) (-f)" using f_def by auto
  moreover have "-e \<noteq> 0" using assms by auto
  ultimately show ?thesis using rel_err.intros assms by metis
qed

lemma rel_neg_prop1_ia:
  assumes "r1 \<in> R1" and "rel_err p i ex r1"
      and "e1 \<in> E1" and "exact_eval i ex e1"
      and "rel_err p i (Neg ex) r2"
    shows "r2 \<in> R1"
  using assms rel_err_unique rel_neg_prop1 by metis

lemma rel_rnd_prop1:
  assumes "rel_err p i ex r"
      and "exact_eval i ex e"
      and "rnd_eval p i ex f"
    shows "rel_err p i (Rnd ex s) (r + p f s / e)"
proof -
  have "rnd_eval p i (Rnd ex s) (f + p f s)" using assms by blast
  moreover have "exact_eval i (Rnd ex s) e" using assms by blast
  moreover have "e \<noteq> 0" using assms by blast
  ultimately have 1: "rel_err p i (Rnd ex s) ((f + p f s - e) / e)" by force
  have "(f + p f s - e) / e = (f - e) / e + p f s / e" by argo
  hence "(f + p f s - e) / e = r + p f s / e" using assms by blast
  thus ?thesis using 1 by simp
qed

lemma rel_rnd_prop1_ia:
  assumes "r1 \<in> R1" and "rel_err p i ex r1"
      and "e1 \<in> E1" and "exact_eval i ex e1"
      and "f1 \<in> F1" and "rnd_eval p i ex f1"
      and "rel_err p i (Rnd ex s) r2"
      and "ia_s_model p S"
    shows "r2 \<in> R1 +\<^sub>I S F1 s"
proof -
  have neq: "e1 \<noteq> 0" using assms by blast
  have "r2 = r1 + p f1 s / e1" using assms rel_rnd_prop1 rel_err_unique by metis
  moreover have "r1 + p f1 s / e1 \<in> R1 +\<^sub>I S F1 s" using assms neq unfolding ia_s_model_def by simp
  ultimately show ?thesis by simp
qed

section \<open>Correctness Theorems\<close>

theorem E_correct: "exact_eval i ex exact \<Longrightarrow> in_box i I \<Longrightarrow> exact \<in> E I ex"
  by (induction rule: exact_eval.induct) (simp_all add: in_box_def)

theorem F_correct: "rnd_eval p i ex rnd \<Longrightarrow> in_box i I \<Longrightarrow> ia_p_model p P \<Longrightarrow> rnd \<in> F P I ex"
  by (induction rule: rnd_eval.induct) (simp_all add: in_box_def ia_p_model_def)

theorem A_correct:
  assumes "add_err p i ex a" and "in_box i I" and "ia_p_model p P"
  shows "a \<in> A P I ex" using assms
proof (induction ex arbitrary: a)
  case (Add lhs rhs)
  from this obtain a1 a2 where
    "a1 \<in> A P I lhs" and "add_err p i lhs a1" and
    "a2 \<in> A P I rhs" and "add_err p i rhs a2" by auto
  hence "a \<in> A P I lhs +\<^sub>I A P I rhs" using Add add_add_prop1_ia by meson
  thus ?case by simp
next
  case (Mul lhs rhs)
  from this E_correct obtain a1 a2 e1 e2 where
    "a1 \<in> A P I lhs" and "add_err p i lhs a1" and
    "a2 \<in> A P I rhs" and "add_err p i rhs a2" and
    "e1 \<in> E I lhs" and "exact_eval i lhs e1" and
    "e2 \<in> E I rhs" and "exact_eval i rhs e2" by blast
  hence "a \<in> A P I lhs *\<^sub>I E I rhs +\<^sub>I E I lhs *\<^sub>I A P I rhs + A P I lhs *\<^sub>I A P I rhs"
    using Mul add_mul_prop1_ia by meson
  thus ?case by simp
next
  case (Div lhs rhs)
  from this E_correct obtain a1 a2 e1 e2 r2 where
    "a1 \<in> A P I lhs" and "add_err p i lhs a1" and
    "a2 \<in> A P I rhs" and "add_err p i rhs a2" and
    "e1 \<in> E I lhs" and "exact_eval i lhs e1" and
    "e2 \<in> E I rhs" and "e2 \<noteq> 0" and "exact_eval i rhs e2" and
    "rnd_eval p i rhs r2" and "r2 \<noteq> 0" by blast
  moreover from this have "r2 \<in> E I rhs +\<^sub>I A P I rhs" using add_exact_to_rnd_ia by meson
  ultimately have "a \<in> (A P I lhs *\<^sub>I E I rhs -\<^sub>I E I lhs *\<^sub>I A P I rhs)
                       \<div>\<^sub>I (E I rhs *\<^sub>I (E I rhs +\<^sub>I A P I rhs))"
    using Div add_div_prop1_ia by meson
  thus ?case by simp
next
  case (Neg ex)
  from this obtain a1 where "a1 \<in> A P I ex" and "add_err p i ex a1" by blast
  hence "a \<in> -\<^sub>IA P I ex" using Neg add_neg_prop1_ia by meson
  thus ?case by simp
next
  case (Rnd ex s)
  from this obtain a1 e1 r1 where
    "a1 \<in> A P I ex" and "add_err p i ex a1" and
    "e1 \<in> E I ex" and "exact_eval i ex e1" and
    "rnd_eval p i ex r1" using E_correct by blast
  moreover from this have "r1 \<in> E I ex +\<^sub>I A P I ex" using add_exact_to_rnd_ia by meson
  ultimately have "a \<in> A P I ex +\<^sub>I P (E I ex +\<^sub>I A P I ex) s" using Rnd add_rnd_prop1_ia by meson
  thus ?case by simp
qed auto

theorem R_correct:
  assumes "rel_err p i ex r" and "in_box i I" and "ia_s_model p S"
    and "R_pre I ex"
  shows "r \<in> R S I ex" using assms
proof (induction ex arbitrary: r)
  case (Add lhs rhs)
  from Add.prems E_correct obtain e1 e2 where
    "e1 \<in> E I lhs" and e1_def: "exact_eval i lhs e1" and
    "e2 \<in> E I rhs" and e2_def: "exact_eval i rhs e2" by blast
  moreover from this Add obtain r1 r2 where
    "rel_err p i lhs r1" and "r1 \<in> R S I lhs" and
    "rel_err p i rhs r2" and "r2 \<in> R S I rhs" by auto
  moreover have "e1 + e2 \<noteq> 0" using e1_def e2_def Add.prems by blast
  ultimately have "r \<in> (E I lhs \<div>\<^sub>I (E I lhs +\<^sub>I E I rhs)) *\<^sub>I R S I lhs
                       +\<^sub>I (E I rhs \<div>\<^sub>I (E I lhs +\<^sub>I E I rhs)) *\<^sub>I R S I rhs"
    using Add.prems rel_add_prop1_ia by meson
  thus ?case by simp
next
  case (Mul lhs rhs)
  from Mul.prems E_correct obtain e1 e2 where
    "e1 \<in> E I lhs" and e1_def: "exact_eval i lhs e1" and
    "e2 \<in> E I rhs" and e2_def: "exact_eval i rhs e2" by blast
  moreover from this Mul obtain r1 r2 where
    "rel_err p i lhs r1" and "r1 \<in> R S I lhs" and
    "rel_err p i rhs r2" and "r2 \<in> R S I rhs" by auto
  moreover have "e1 * e2 \<noteq> 0" using e1_def e2_def Mul.prems by blast
  ultimately have "r \<in> R S I lhs +\<^sub>I R S I rhs +\<^sub>I R S I lhs *\<^sub>I R S I rhs"
    using Mul.prems rel_mul_prop1_ia by meson
  thus ?case by simp
next
  case (Div lhs rhs)
  from Div.prems E_correct obtain e1 e2 where
    e1_in: "e1 \<in> E I lhs" and e1_def: "exact_eval i lhs e1" and
    e2_in: "e2 \<in> E I rhs" and e2_def: "exact_eval i rhs e2" by blast
  moreover from this Div obtain r1 r2 f2 where
    "rel_err p i lhs r1" and "r1 \<in> R S I lhs" and
    "rel_err p i rhs r2" and "r2 \<in> R S I rhs" and
    "rnd_eval p i rhs f2" and "f2 \<noteq> 0" by auto
  moreover from this have "f2 \<in> E I rhs *\<^sub>I ({1} +\<^sub>I R S I rhs)"
    using rel_exact_to_rnd_ia e2_def e2_in by meson
  moreover have "e1 / e2 \<noteq> 0" using e1_def e2_def Div.prems by blast
  ultimately have "r \<in> (R S I lhs -\<^sub>I R S I rhs) \<div>\<^sub>I ({1} +\<^sub>I R S I rhs)"
    using Div.prems rel_div_prop1_ia by meson
  thus ?case by simp
next
  case (Neg ex)
  from Neg.prems E_correct obtain e1 where
    "e1 \<in> E I ex" and "exact_eval i ex e1" by blast
  moreover from this Neg obtain r1 where
    "r1 \<in> R S I ex" and "rel_err p i ex r1" by auto
  ultimately have "r \<in> R S I ex" using Neg.prems rel_neg_prop1_ia by meson
  thus ?case by simp
next
  case (Rnd ex s)
  from Rnd.prems E_correct obtain e1 where
    e1_in: "e1 \<in> E I ex" and e1_def: "exact_eval i ex e1" by blast
  moreover from this Rnd obtain r1 f1 where
    "r1 \<in> R S I ex" and "rel_err p i ex r1" and "rnd_eval p i ex f1" by auto
  moreover from this have "f1 \<in> E I ex *\<^sub>I ({1} +\<^sub>I R S I ex)"
    using rel_exact_to_rnd_ia e1_in e1_def by meson
  ultimately have "r \<in> R S I ex +\<^sub>I S (E I ex *\<^sub>I ({1} +\<^sub>I R S I ex)) s"
    using Rnd.prems rel_rnd_prop1_ia by meson
  thus ?case by simp
qed auto

theorem AU_RU_correct:
  assumes "in_box i I" and "ia_p_model p P" and "ia_s_model p S"
  shows "\<And> a. add_err p i ex a \<Longrightarrow> a \<in> AU P S I ex"
   and  "\<And> r. rel_err p i ex r \<Longrightarrow> r \<in> RU P S I ex"
   and  "\<And> a. add_err p i ex a \<Longrightarrow> a \<in> AU0 P S I ex"
   and  "\<And> r. rel_err p i ex r \<Longrightarrow> RU0_ok I ex \<Longrightarrow> r \<in> RU0 P S I ex"
  using assms
proof (induction P S I ex and P S I ex and P S I ex and P S I ex rule: AU_RU_AU0_RU0.induct)
  case (1 P S I ex)
  show "a \<in> AU P S I ex"
  proof (cases "RU0_ok I ex")
    case False
    thus ?thesis using 1 by simp
  next
    case True
    from this 1 E_correct obtain e1 where
      e1_in: "e1 \<in> E I ex" and e1_def: "exact_eval i ex e1" by blast
    hence "e1 \<noteq> 0" using True by (cases ex) auto
    from this e1_def 1 True obtain r1 where
      r1_in: "r1 \<in> RU0 P S I ex" and r1_def: "rel_err p i ex r1" by auto
    hence "a \<in> RU0 P S I ex *\<^sub>I E I ex" using e1_in e1_def "1.prems" add_from_rel_err_ia by meson
    moreover have "a \<in> AU0 P S I ex" using 1 True by blast
    ultimately show ?thesis using ia_intersect_inc by simp
  qed
next
  case (2 P S I ex)
  from this E_correct obtain e1 where
    "e1 \<in> E I ex" and e1_def: "exact_eval i ex e1" by blast
  moreover from this 2 obtain a1 where 
    "a1 \<in> AU0 P S I ex" and "add_err p i ex a1" by blast
  ultimately have from_a: "r \<in> AU0 P S I ex \<div>\<^sub>I E I ex" using rel_from_add_err_ia "2.prems" by meson
  show "r \<in> RU P S I ex"
  proof (cases "RU0_ok I ex")
    case True
    hence r_in: "r \<in> RU0 P S I ex" using 2 by blast
    thus ?thesis using r_in from_a ia_intersect_inc by simp
  next
    case False
    thus ?thesis using "2.prems" from_a by simp
  qed
next
  case (3 P S I lhs rhs)
  from this obtain a1 a2 where
    "a1 \<in> AU P S I lhs" and "add_err p i lhs a1" and
    "a2 \<in> AU P S I rhs" and "add_err p i rhs a2" by auto
  hence "a \<in> AU P S I lhs +\<^sub>I AU P S I rhs" using 3 add_add_prop1_ia by meson
  thus ?case by simp
next
  case (4 P S I lhs rhs)
  from "4.IH"(1,2) "4.prems" E_correct obtain a1 a2 e1 e2 where
    "a1 \<in> AU P S I lhs" and "add_err p i lhs a1" and
    "a2 \<in> AU P S I rhs" and "add_err p i rhs a2" and
    "e1 \<in> E I lhs" and "exact_eval i lhs e1" and
    "e2 \<in> E I rhs" and "exact_eval i rhs e2" by blast
  hence "a \<in> AU P S I lhs *\<^sub>I E I rhs +\<^sub>I E I lhs *\<^sub>I AU P S I rhs + AU P S I lhs *\<^sub>I AU P S I rhs"
    using add_mul_prop1_ia "4.prems" by meson
  thus ?case by simp
next
  case (5 P S I lhs rhs)
  from "5.prems" "5.IH"(1,2) E_correct obtain a1 a2 e1 e2 f2 where
    "a1 \<in> AU P S I lhs" and "add_err p i lhs a1" and
    "a2 \<in> AU P S I rhs" and "add_err p i rhs a2" and
    "e1 \<in> E I lhs" and "exact_eval i lhs e1" and
    "e2 \<in> E I rhs" and "e2 \<noteq> 0" and "exact_eval i rhs e2" and
    "rnd_eval p i rhs f2" and "f2 \<noteq> 0" by blast
  moreover from this have "f2 \<in> E I rhs +\<^sub>I AU P S I rhs" using add_exact_to_rnd_ia by meson
  ultimately have "a \<in> (AU P S I lhs *\<^sub>I E I rhs -\<^sub>I E I lhs *\<^sub>I AU P S I rhs)
                       \<div>\<^sub>I (E I rhs *\<^sub>I (E I rhs +\<^sub>I AU P S I rhs))"
    using "5.prems" add_div_prop1_ia by meson
  thus ?case by simp
next
  case (6 P S I ex)
  from this obtain a1 where "a1 \<in> AU P S I ex" and "add_err p i ex a1" by blast
  hence "a \<in> -\<^sub>IAU P S I ex" using "6.prems" add_neg_prop1_ia by meson
  thus ?case by simp
next
  case (7 P S I ex s)
  from this obtain a1 e1 r1 where
    "a1 \<in> AU P S I ex" and "add_err p i ex a1" and
    "e1 \<in> E I ex" and "exact_eval i ex e1" and
    "rnd_eval p i ex r1" using E_correct by blast
  moreover from this have "r1 \<in> E I ex +\<^sub>I AU P S I ex" using add_exact_to_rnd_ia by meson
  ultimately have "a \<in> AU P S I ex +\<^sub>I P (E I ex +\<^sub>I AU P S I ex) s"
    using "7.prems" add_rnd_prop1_ia by meson
  thus ?case by simp
next
  case (10 P S I lhs rhs)
  from "10.prems" E_correct obtain e1 e2 where
    "e1 \<in> E I lhs" and e1_def: "exact_eval i lhs e1" and
    "e2 \<in> E I rhs" and e2_def: "exact_eval i rhs e2" by blast
  moreover from this 10 obtain r1 r2 where
    "rel_err p i lhs r1" and "r1 \<in> RU P S I lhs" and
    "rel_err p i rhs r2" and "r2 \<in> RU P S I rhs" by auto
  moreover have "e1 + e2 \<noteq> 0" using e1_def e2_def "10.prems" by blast
  ultimately have "r \<in> (E I lhs \<div>\<^sub>I (E I lhs +\<^sub>I E I rhs)) *\<^sub>I RU P S I lhs
                       +\<^sub>I (E I rhs \<div>\<^sub>I (E I lhs +\<^sub>I E I rhs)) *\<^sub>I RU P S I rhs"
    using "10.prems" rel_add_prop1_ia by meson
  thus ?case by simp
next
  case (11 P S I lhs rhs)
  from "11.prems" E_correct obtain e1 e2 where
    "e1 \<in> E I lhs" and e1_def: "exact_eval i lhs e1" and
    "e2 \<in> E I rhs" and e2_def: "exact_eval i rhs e2" by blast
  moreover from this 11 obtain r1 r2 where
    "rel_err p i lhs r1" and "r1 \<in> RU P S I lhs" and
    "rel_err p i rhs r2" and "r2 \<in> RU P S I rhs" by auto
  moreover have "e1 * e2 \<noteq> 0" using e1_def e2_def "11.prems" by blast
  ultimately have "r \<in> RU P S I lhs +\<^sub>I RU P S I rhs +\<^sub>I RU P S I lhs *\<^sub>I RU P S I rhs"
    using "11.prems" rel_mul_prop1_ia by meson
  thus ?case by simp
next
  case (12 P S I lhs rhs)
  from "12.prems" E_correct obtain e1 e2 where
    e1_in: "e1 \<in> E I lhs" and e1_def: "exact_eval i lhs e1" and
    e2_in: "e2 \<in> E I rhs" and e2_def: "exact_eval i rhs e2" by blast
  moreover from this 12 obtain r1 r2 f2 where
    "rel_err p i lhs r1" and "r1 \<in> RU P S I lhs" and
    "rel_err p i rhs r2" and "r2 \<in> RU P S I rhs" and
    "rnd_eval p i rhs f2" and "f2 \<noteq> 0" by auto
  moreover from this have "f2 \<in> E I rhs *\<^sub>I ({1} +\<^sub>I RU P S I rhs)"
    using rel_exact_to_rnd_ia e2_def e2_in by meson
  moreover have "e1 / e2 \<noteq> 0" using e1_def e2_def "12.prems" by blast
  ultimately have "r \<in> (RU P S I lhs -\<^sub>I RU P S I rhs) \<div>\<^sub>I ({1} +\<^sub>I RU P S I rhs)"
    using "12.prems" rel_div_prop1_ia by meson
  thus ?case by simp
next
  case (13 P S I ex)
  from "13.prems" E_correct obtain e1 where
    "e1 \<in> E I ex" and "exact_eval i ex e1" by blast
  moreover from this 13 obtain r1 where
    "r1 \<in> RU P S I ex" and "rel_err p i ex r1" by auto
  ultimately have "r \<in> RU P S I ex" using "13.prems" rel_neg_prop1_ia by meson
  thus ?case by simp
next
  case (14 P S I ex s)
  from "14.prems" E_correct obtain e1 where
    e1_in: "e1 \<in> E I ex" and e1_def: "exact_eval i ex e1" by blast
  moreover from this 14 obtain r1 f1 where
    "r1 \<in> RU P S I ex" and "rel_err p i ex r1" and "rnd_eval p i ex f1" by auto
  moreover from this have "f1 \<in> E I ex *\<^sub>I ({1} +\<^sub>I RU P S I ex)"
    using rel_exact_to_rnd_ia e1_in e1_def by meson
  ultimately have "r \<in> RU P S I ex +\<^sub>I S (E I ex *\<^sub>I ({1} +\<^sub>I RU P S I ex)) s"
    using "14.prems" rel_rnd_prop1_ia by meson
  thus ?case by simp
qed auto

inductive add_adj :: "(real \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 's Expr \<Rightarrow> 's Expr \<Rightarrow> real \<Rightarrow> bool" where
"add_err p i sub a \<Longrightarrow> add_err p i ex (adj * a) \<Longrightarrow> add_adj p i ex sub adj"

fun parents :: "'s Expr \<Rightarrow> 's Expr \<Rightarrow> 's Expr set" where
"parents (Add lhs rhs) sub = parents lhs sub \<union> parents rhs sub \<union> (if lhs = sub \<or> rhs = sub then {Add lhs rhs} else {})" |
"parents (Mul lhs rhs) sub = parents lhs sub \<union> parents rhs sub \<union> (if lhs = sub \<or> rhs = sub then {Mul lhs rhs} else {})" |
"parents (Div lhs rhs) sub = parents lhs sub \<union> parents rhs sub \<union> (if lhs = sub \<or> rhs = sub then {Div lhs rhs} else {})" |
"parents (Neg ex) sub = parents ex sub \<union> (if ex = sub then {Neg ex} else {})" |
"parents (Rnd ex s) sub = parents ex sub \<union> (if ex = sub then {Rnd ex s} else {})" |
"parents (Const c) sub = {}" |
"parents (Var x) sub = {}"

fun leafs :: "'s Expr \<Rightarrow> 's Expr set" where 
"leafs (Add lhs rhs) = leafs lhs \<union> leafs rhs" |
"leafs (Mul lhs rhs) = leafs lhs \<union> leafs rhs" |
"leafs (Div lhs rhs) = leafs lhs \<union> leafs rhs" |
"leafs (Neg ex) = leafs ex" |
"leafs (Rnd ex s) = leafs ex \<union> {Rnd ex s}" |
"leafs (Const c) = {}" |
"leafs (Var x) = {}"

lemma parents_finite [simp]: "finite (parents ex sub)"
  by (induction ex) auto

lemma leafs_finite [simp]: "finite (leafs ex)"
  by (induction ex) auto

fun A_leaf :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set" where
"A_leaf P I (Rnd ex s) = P (E I ex +\<^sub>I A P I ex) s" |
"A_leaf P I _ = {0}"

(* TODO: Div *)
fun A_bar :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> 's Expr \<Rightarrow> real set" where
"A_bar P I (Add lhs rhs) sub =
  (if sub = lhs then {1}
   else if sub = rhs then {1}
   else {0})" |
"A_bar P I (Mul lhs rhs) sub =
  (if sub = lhs then E I rhs +\<^sub>I (A P I rhs \<div>\<^sub>I {2})
   else if sub = rhs then E I lhs +\<^sub>I (A P I lhs \<div>\<^sub>I {2})
   else 0)" |
"A_bar P I (Div lhs rhs) sub =
  (if sub = lhs \<and> sub = rhs then {0}
   else if sub = lhs then E I rhs +\<^sub>I (A P I rhs \<div>\<^sub>I {2})
   else if sub = rhs then E I lhs +\<^sub>I (A P I lhs \<div>\<^sub>I {2})
   else 0)" |
"A_bar P I (Neg ex) sub = (if sub = ex then -\<^sub>IA P I ex else {0})" |
"A_bar P I (Rnd ex s) sub = (if sub = ex then A P I ex else {0})" |
"A_bar P I (Const c) ex = {0}" |
"A_bar P I (Var x) ex = {0}"

function A_tilde :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> 's Expr \<Rightarrow> real set" where
  "A_tilde P I ex sub = (\<Sum>prnt\<in>parents ex sub. A_tilde P I ex prnt *\<^sub>I A_bar P I prnt sub)" (* TODO: this is currently not using the interval sum *)
  by auto

lemma size_diff_is_A_tilde_measure:
  assumes "prnt \<in> parents ex sub"
  shows "size ex - size prnt < size ex - size sub \<and> 0 \<le> size ex - size prnt" using assms
proof (induction ex sub rule: parents.induct)
  case (1 lhs rhs sub)
  thus ?case by (cases "lhs = sub \<or> rhs = sub") auto
next
  case (2 lhs rhs sub)
  thus ?case by (cases "lhs = sub \<or> rhs = sub") auto
next
  case (3 lhs rhs sub)
  thus ?case by (cases "lhs = sub \<or> rhs = sub") auto
next
  case (4 ex sub)
  thus ?case by (cases "ex = sub") auto
next
  case (5 ex s sub)
  thus ?case by (cases "ex = sub") auto
qed auto

termination A_tilde
  using size_diff_is_A_tilde_measure
  by (relation "measure (\<lambda>(P, I, ex, sub). size ex - size sub)") auto

thm A_tilde.induct

(*fun A_prime :: "(real set \<Rightarrow> 's \<Rightarrow> real set) \<Rightarrow> (nat \<Rightarrow> real set) \<Rightarrow> 's Expr \<Rightarrow> real set" where
"A_prime P I ex = \<Sum> { A_tilde P I ex leaf *\<^sub>I A_leaf P I leaf | leaf. leaf \<in> leafs ex }"*)

lemma A_tilde_correct:
  assumes "add_err p i ex a1"
      and "add_err p i sub a2"
      and "add_adj p i ex sub adj"
    shows "adj \<in> A_tilde P I ex sub"
  apply (induction arbitrary: adj rule: A_tilde.induct)


end