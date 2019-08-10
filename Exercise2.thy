theory Exercise2
  imports Main
begin
declare [[names_short]]
(* 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* 2.2 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

theorem add_assoc [simp]: "add (add l m) n = add l (add m n)"
  apply(induction l)
  apply(auto)
  done

lemma add_0 [simp]: "add m 0 = m"
  apply(induction m)
  apply(auto)
  done

lemma add_suc [simp]: "add n (Suc m) = Suc (add n m)"
  apply(induction n)
  apply(auto)
  done

theorem add_commut [simp]: "add m n = add n m"
  apply(induction m)
  apply(auto)
  done
    
fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc (Suc (double n))"
  
theorem double_add [simp]: "double m = add m m"
  apply(induction m)
  apply(auto)
  done
    
(* 2.3 *)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x [] = 0" |
  "count x (y # xs) = add (count x xs) (if x=y then 1 else 0)"
  
theorem count_length_constraint: "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done
    
(* 2.4*)
    
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]" |
  "snoc (y # ys) x = y # (snoc ys x)"
  
fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x # xs) = snoc (reverse xs) x"
  
lemma reverse_snoc [simp]: "reverse (snoc xs a) = a # (reverse xs)"
  apply(induction xs)
  apply(auto)
  done

lemma rev_snoc [simp]: "rev (snoc xs a) = a # (rev xs)"
  apply(induction xs)
  apply(auto)
  done

theorem reverse_reverse [simp]: "reverse(reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done
    
(* 2.5 *)
    
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = (Suc n) + (sum_upto n)"
  
theorem sum_upto_closed_form [simp]: "sum_upto n = n * (n+1) div 2"
  apply(induction n)
  apply(auto)
  done
    
(* 2.6 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l a r) = a # (contents l) @ (contents r)"
  
fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node l n r) = n + (sum_tree l) + (sum_tree r)"
  
theorem contents_sum_tree_rel: "sum_tree t = sum_list (contents t)"
  apply(induction t)
  apply(auto)
  done
    
(* 2.7 *)

datatype 'a tree2 = Leaf 'a | Node "'a tree2" 'a "'a tree2"


fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Leaf x) = Leaf x" |
(* "mirror (Node l x r) = Node r x l" *)
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

(* https://www.geeksforgeeks.org/tree-traversals-inorder-preorder-and-postorder/ *)

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf x) = [x]" |
"pre_order (Node l x r) = x # (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leaf x) = [x]" |
"post_order (Node l x r) = snoc (post_order l @ post_order r) x" 
(*"post_order (Node l x r) = post_order l @ post_order r @ [x]"*)

(* example case *)
value "(Node (Node (Leaf 4) 2 (Leaf 5)) (1::nat) (Leaf 3))"
value "mirror (Node (Node (Leaf 4) 2 (Leaf 5)) (1::nat) (Leaf 3))"
(* 1 2 4 5 3 *)
value "pre_order (Node (Node (Leaf 4) 2 (Leaf 5)) (1::nat) (Leaf 3))"
(* 4 5 2 3 1 *)
value "post_order (Node (Node (Leaf 4) 2 (Leaf 5)) (1::nat) (Leaf 3))"


(* why snoc version doesn't work? *)
(*It was due the reverse_snoc lemma only simplifies reverse and snoc 
not rev and snoc after prove the equivalent theorem for rev and snoc 
it works as expected.*)
(*Which invoked me to test with reverse version*)
(*Which needs additional lemma as expected. Now we can prove \<down> first
and then*)

lemma reverse_snoc2[simp]: "xs @ snoc ys a = snoc (xs @ ys) a"
  apply(induction xs)
  apply(simp_all)
  done

lemma reverse_app[simp]: "(reverse xs) @ (reverse ys) = reverse (ys @ xs)"
 apply(induction ys)
 apply(auto)
 done 


lemma pre_post_rel: "pre_order (mirror t) = reverse (post_order t)"
  apply(induction t)
  apply(auto)
  done

(* done! *)

(* 2.8 *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []" |
  "intersperse a (x # xs) = x # a # (intersperse a xs)"
  
lemma intersperse_map:
 "map f (intersperse a xs) =intersperse (f a) (map f xs)"
  apply(induction xs)
  apply(auto)
  done
    
(* 2.9 *)
    
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 n = n" |
  "itadd (Suc m) n = itadd m (Suc n)"
  
lemma itadd_really_add: "itadd m n = add m n"
  (* apply(induction m) *)
  (* apply(auto) *)
    (* \<up> we need generalization to allow the n to be free variable. *)
  apply(induction m arbitrary: n)
  apply(auto)
  done
    
(*2.10*)
    
datatype tree0 = Tip | Node tree0 tree0
  
fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 1" |
  "nodes (Node l r) = 1 + (nodes l) + (nodes r)"
  
fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t"|
  "explode (Suc n) t = explode n (Node t t)"
  
(*experiment with some example*)
  
value "nodes (explode 5 (Node Tip Tip))"
value "nodes (explode 9 Tip)"

(*by the above experiment we guess that when t=Tip,
the return number = 2^(n+1) - 1 *) 

(*by solving the differential equation--f_(n+1) = 2 f_n + 1-- we get
f_n = (f_0 + 1)*2^n -1*)

theorem node_number_explode[simp]:
  "nodes (explode n t) = 2^n * ((nodes t) + 1) - 1"
  apply(induction n arbitrary: t)
  apply(auto simp add: algebra_simps)
  done

(*Exercise 2.11*)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval (Const num) _ = num" |
"eval Var x = x " |
"eval (Add l r) x = (eval l x) + (eval r x)" |
"eval (Mult l r) x = (eval l x) * (eval r x)"

(*fun itevalp :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
"itevalp [] _ _ result = result" |
"itevalp (c#cs) x n result = itevalp cs x (n+1) (result + c*x^n)"

fun evalp_recur :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
"evalp_recur [] _ _  = 0" |
"evalp_recur (c#cs) x n = c*x^n + evalp_recur cs x (n+1)"


definition evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp cs x = itevalp cs x 0 0"*)
(*"evalp cs x = evalp_recur cs x 0"*)

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x  = 0"|
"evalp (c # cs) x = c + x*(evalp cs x)"

(*test*)
(*value "evalp [4, 2, -1, 3] 5"*)
(*works*)

fun intList_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"intList_add [] ys = ys"|
"intList_add xs [] = xs"|
"intList_add (x#xs) (y#ys) = (x + y) # intList_add xs ys"

(*test*)
(*value "intList_add [2, 1, 5] [1, -2]"*)

fun intList_times_int :: "int list \<Rightarrow> int \<Rightarrow> int list" where
"intList_times_int [] _ = []"|
"intList_times_int (x#xs) c = (c * x) # (intList_times_int xs c)"

(*fun pad_ntime :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"pad_ntime xs 0 = xs"|
"pad_ntime [] _ = []"|
"pad_ntime xs (Suc n) = 0 # (pad_ntime xs n)"

fun itIntListMul :: "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list" where
"itIntListMul xs [] _ result = result"|
"itIntListMul xs (y#ys) n result = 
itIntListMul xs ys (n + 1) 
(if y\<noteq>0 then 
(intList_add (intList_times_int (pad_ntime xs n) y) result)
else result)"

definition intList_mul :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"intList_mul xs ys = itIntListMul xs ys 0 []"*)

fun intList_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"intList_mult xs [] = []"|
"intList_mult xs (y#ys) = intList_add (intList_times_int xs y)
(0 # (intList_mult xs ys))"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]"|
"coeffs (Const num) = [num]"|
"coeffs (Add l r) = intList_add (coeffs l) (coeffs r)"|
"coeffs (Mult l r) = intList_mult (coeffs l) (coeffs r)"

(*value "coeffs (Add Var (Mult Var Var))"*)

(*Hint: consider the hint in Exercise 2.10*)

lemma evalp_add_coeffs [simp]: "evalp (intList_add xs ys) a = (evalp xs a) + (evalp ys a)"
  apply(induction rule: intList_add.induct)
  apply(auto simp add:algebra_simps)
  done

lemma evalp_scala_coeffs [simp]: "evalp (intList_times_int xs c) a = (evalp xs a) * c"
apply(induction xs)
apply(auto simp add: algebra_simps)
done

lemma evalp_mul_coeffs [simp]: "evalp (intList_mult xs ys) a = (evalp xs a) * (evalp ys a)"
apply(induction ys)
apply(auto simp add: algebra_simps)
done

theorem evalp_coeffs [simp]: "evalp (coeffs e) x = eval e x"
  apply(induction e)
  apply(auto)
  done
