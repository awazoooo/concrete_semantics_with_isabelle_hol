theory Chapter4
  imports Main
begin

(* Ex 4.1 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}"
| "set (Node l a r) = set l \<union> {a} \<union> set r"

(* fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True"
| "ord (Node l a r) = 
*) 

lemma "\<forall>x. \<exists>y. x = y"
  by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
  by auto

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n + n"
  by fastforce

lemma "\<lbrakk> \<forall>x y. T x y \<or> T y x;
        \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
        \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk>
        \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
  by blast

lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"
  sledgehammer
  using append_eq_append_conv by blast

lemma "\<lbrakk> (a::nat) \<le> x + b; 2 * x < c \<rbrakk> \<Longrightarrow> 2 * a + 1 \<le> 2 * b + c" 
  by arith

lemma "\<lbrakk> (a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e \<rbrakk> \<Longrightarrow> a \<le> e"
  by (blast intro: le_trans)

thm conjI[OF refl[of "a"] refl[of "b"]]

lemma "Suc (Suc (Suc a)) \<le> b \<Longrightarrow> a \<le> b"
  by (blast dest: Suc_leD)

inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0"
| evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma "ev (Suc (Suc (Suc (Suc 0))))"
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done

lemma "ev m \<Longrightarrow> evn m"
  apply (induction rule: ev.induct)
by simp_all

lemma "evn n \<Longrightarrow> ev n"
  apply (induction n rule: evn.induct)
  apply (simp_all add: ev0 evSS)
done

declare ev.intros[simp,intro]

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
  apply assumption
  apply (metis step)
done

(* Ex 4.2 *)

inductive palindrome :: "'a list \<Rightarrow> bool" where
  emp: "palindrome []"
| singleton: "palindrome [a]"
| multi: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply (induction rule: palindrome.induct)
  apply simp_all
done

(* Ex 4.5 *)
datatype alpha = a | b

inductive S  where
  empty: "S []"
| betw: "S w \<Longrightarrow> S (a # w @ [b])"
| conc : "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"

inductive T where
  empty: "T []"
| betw_conc: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ a # w2 @ [b])"

lemma T_S:  "T w \<Longrightarrow> S w"
  apply (induct rule: T.induct)
  apply (rule S.empty)
  apply (metis S.conc S.betw)
done

axiomatization where 
T_app: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ w2)"

  
lemma S_T: "S w \<Longrightarrow> T w"
  apply (induct rule: S.induct)
  apply (rule T.empty)
  using T.simps append.left_neutral apply blast
  apply (simp add: T_app)
done

theorem S_T_eq: "S w = T w"
  apply auto
  apply (rule S_T, assumption)
  apply (rule T_S, assumption)
done