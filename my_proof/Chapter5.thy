theory Chapter5
imports Main
begin

(* jEdit(1) *)
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by auto
  from 1 have 2: "\<exists>a. {x. x \<notin> f x } = f a" by auto
  from 2 show "False" by auto
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by auto
  from this show "False" by auto
qed

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof 
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by auto
  thus "False" by auto
qed

lemma
  fixes f:: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof- 
  have "\<exists>a. {x. x \<notin> f x} = f a" using s
    by auto
  thus "False" by auto
qed

(* obtain *)
lemma "\<not> surj (f:: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x. x \<notin> f x} = f a" by auto
  then obtain a where "{x. x \<notin> f x} = f a" by auto
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by auto
  thus "False" by auto
qed

(* case analysis *)
lemma
  fixes P:: "bool"
  shows "P = True \<or> P = False"
proof (cases P)
  case True
  then show ?thesis by auto
  next
  case False
  then show ?thesis by auto
qed
  
thm dvd_def

value "(18::nat) dvd 9"
value "(18::nat) dvd 36"

(* raw proof block *)
lemma 
  fixes a b :: int
  assumes "b dvd (a + b)" shows "b dvd a"
proof -
  { fix k
    assume k : "a + b = b * k"
    have "\<exists>k'. a = b * k'"
    proof
      show "a = b * (k - 1)" using k by (simp add: algebra_simps)
    qed
  }
  then show ?thesis using assms by (auto simp add: dvd_def)
qed

(* Ex 5.1 *)
lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
proof cases
  assume "T x y" 
  thus "T x y" by auto
next
  assume "\<not> T x y"
  then have "T y x" using T by auto
  then have "A y x" using TA by auto
  then have "x = y" using assms by auto 
  thus "T x y" using T by auto
qed

(* Ex 5.2 *)
(* lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs) \<or>
       (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof (induction xs) 
  sorry *)

(* datatype case analysis *)
lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []" (* Nil *)
  thus ?thesis by simp
next
  fix y ys
  assume "xs = y # ys" (* Cons y ys *)
  thus ?thesis by simp
qed
  
(* structural induction *)
lemma "\<Sum> {0..n::nat} = n * (n + 1) div 2"
proof (induction n)
  show "\<Sum> {0..0::nat} = 0 * (0 + 1) div 2" by simp
next
  fix n
  assume "\<Sum> {0..n::nat} = n * (n + 1) div 2"
  thus "\<Sum> {0..Suc n} = Suc n * (Suc n + 1) div 2" by simp
qed

lemma "\<Sum> {0..n::nat} = n * (n + 1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n
  assume "?P n"
  thus "?P (Suc n)" by simp
qed

(* rule induction *)

inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0"
| evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
proof (induction rule: ev.induct)
  case ev0 
  show ?case by simp
next
  case evSS
  from this show ?case by simp
qed

lemma "ev n \<Longrightarrow> evn n"
proof (induction rule: ev.induct)
  case ev0
  then show ?case by simp
next
  case (evSS n)
  have "evn (Suc (Suc n)) = evn n" by simp
  thus ?case using `evn n` by blast
qed

(* rule inversion *)
lemma "\<not> ev (Suc 0)"
proof 
  assume "ev (Suc 0)" 
  thus False by cases
qed

lemma 
  assumes a: "ev (Suc (Suc n))"
  shows "ev n"
proof -
  

  

(* simple exeicise *)
lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof 
  assume "ev (Suc (Suc (Suc 0)))"
  thus False
  proof - 
    from this have "ev (Suc 0)" by (simp add: ev.evSS)

(* advanced rule induction *)
lemma "ev (Suc m) \<Longrightarrow> \<not> ev m"
proof (induction "Suc m" arbitrary: m rule: ev.induct)
  fix n 
  assume IH: "\<And>m. n = Suc m \<Longrightarrow> \<not> ev m"
  show "\<not> ev (Suc n)"
  proof 
    assume "ev (Suc n)"
    thus False
    proof cases
      fix k 
      assume "n = Suc k" "ev k"
      thus False using IH by auto
    qed
  qed
qed

end

