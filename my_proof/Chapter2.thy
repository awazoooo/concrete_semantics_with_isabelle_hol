theory Chapter2
imports Main
begin
  
(* jEdit(1) *)  
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_02 : "add m 0 = m"
  apply (induction m)
  apply auto
done
 
thm add_02

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app [] ys = ys"
| "app (x#xs) ys = x # (app xs ys)"
  
value "(app (Cons 0 (Nil::int list)) (Cons 0 Nil))"
  
fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil"
| "rev (Cons x xs) = app (rev xs) (Cons x Nil)"
  
value "rev (Cons True (Cons False Nil))"

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply (induction xs)
  apply auto
done
  
lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  apply auto
done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
  apply auto
done
  
theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply (induction xs)
  apply auto 
done

(* Ex 2.2 *)
lemma add_assoc: "add a (add b c) = add (add a b) c"
  apply (induction a)
  apply auto
  done

lemma add_0[simp]: "add m 0 = m"
  apply (induct m)
  apply auto
done

lemma add_succ[simp]: "Suc (add m n) = add m (Suc n)"
  apply (induct m)
   apply auto
done

lemma add_comm: "add a b = add b a"
  apply (induction a)
  apply auto
done
  
fun double ::  "nat \<Rightarrow> nat" where
  "double 0 = 0"
| "double (Suc m) = Suc (Suc (double m))"

lemma add_double: "double m = add m m"
  apply (induct m)
  apply auto
done

(* Ex 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count v [] = 0"
| "count v (x#xs) = (if v = x then Suc (count v xs) else count v xs)"

lemma count_length_le : "count x xs \<le> length xs"
  apply (induct xs)
  apply auto
done

(* Ex 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] a = [a]"
| "snoc (x#xs) a = x # (snoc xs a)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []"
| "reverse (x#xs) = snoc (reverse xs) x"

value "reverse [(1::nat),2,3,4,5]"

(*lemma reverse_reverse : "reverse (reverse xs) = xs"
  apply (induct xs)
  apply auto*)


(* Ex 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc m) = Suc (m + (sum_upto m))"

value "sum_upto 10"

lemma sum_upto_correct : "sum_upto n = n * (n + 1) div 2"
  apply (induct n)
  apply auto
done 

(* jEdit(2) *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node l v r) = Node (mirror r) v (mirror l)"
  
lemma "mirror (mirror t) = t"
  apply (induction t)
  apply auto
done
 
datatype 'a option = None | Some 'a

value "tl [(1::nat),2,3]"
  
fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "lookup [] key = None"
| "lookup ((a, b) # ps) key = 
     (if key = a then Some b else lookup ps key)"
  
(* jEdit(3) *)
  
fun div2 :: "nat \<Rightarrow> nat" where
  "div2 0 = 0"
| "div2 (Suc 0) = 0"
| "div2 (Suc (Suc n)) = Suc (div2 n)"
  
lemma "div2 n = n div 2"
  apply (induction n rule: div2.induct)
  apply auto
done

(* Ex 2.6 *)

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []"
| "contents (Node l a r) = contents l @ [a] @ contents r"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0"
| "sum_tree (Node l a r) = sum_tree l + a + sum_tree r"

lemma "sum_tree t = sum_list (contents t)"
  apply (induction t)
  apply auto
done

(* Ex 2.7 *)

datatype 'a tree2 = Tip2 'a | Node2 "'a tree2" 'a "'a tree2"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror2 (Tip2 a) = Tip2 a"
| "mirror2 (Node2 l a r) = Node2 (mirror2 r) a (mirror2 l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Tip2 a) = [a]"
| "pre_order (Node2 l a r) = [a] @ (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Tip2 a) = [a]"
| "post_order (Node2 l a r) = (post_order l) @ (post_order r) @ [a]"

(* lemma pre_post : "pre_order (mirror2 t) = reverse (post_order t)"
  apply (induct t)
   apply auto
  *)


(* Ex 2.8 *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []"
| "intersperse a (x#xs) = x # a # (intersperse a xs)"

lemma intersperse_map : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
  apply auto
done
   
(* jEdit(4) *)
  
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys     = ys"
| "itrev (x#xs) ys = itrev xs (x # ys)"

(* can't prove *)  
(*lemma "itrev xs [] = rev xs"
  apply (induction xs)
  apply (auto)
*)

lemma app_att [simp]: "app a b = a @ b"
  apply (induct a)
  apply auto
done
  
lemma "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys) (* add forall in ys *)
  apply auto
done

(* Ex 2.9 *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 n = n"
| "itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_add_eq : "itadd m n = add m n"
  apply (induct m arbitrary:n)
  apply auto
done

(* Ex 2.10 *)

datatype tree0 = Tip0 | Node0 "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip0 = 1"
| "nodes (Node0 l r) = 1 + nodes l + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t"
| "explode (Suc n) t = explode n (Node0 t t)"

(*lemma explode_n : "nodes (explode n t) = (nodes t + 1) * 2 ^ n - 1"
  apply (induct n)
  apply auto
*)

(* Ex 2.11 *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var x = x"
| "eval (Const i) _ = i"
| "eval (Add e1 e2) x = eval e1 x + eval e2 x"
| "eval (Mult e1 e2) x = eval e1 x * eval e2 x"

value "eval (Add Var (Const 3)) 5"

(*fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] _ = 0"
| "evalp [x] _ = x"
| "evalp (x#y#xs) v = x + (evalp xs (v * 2))"

value "evalp [4, 2] 2"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = 1"
| "coeffs (Const i) = *)

end