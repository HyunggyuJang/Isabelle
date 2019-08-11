theory Exercise3
imports Main
begin

(* Abstract Syntax Tree *)
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

(* Evaluate the expression to its value *)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

(* examples *)
value "aval (Plus (N 3) (V ''x'')) (\<lambda>x.0)"
(* value "aval (Plus (N 3) (V ''x'')) (<>)" *)
(* not works *)

(* constant folding *)
fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a1 a2) =
    (case (asimp_const a1, asimp_const a2) of 
        (N n1, N n2) \<Rightarrow> N(n1 + n2) |
        (b1, b2) \<Rightarrow> Plus b1 b2)"

lemma \<open>aval (asimp_const a) s = aval a s\<close>
apply(induction a)
apply(auto split: aexp.split)
done

(* local optimization for plus *)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N (i1 + i2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
apply(induction rule: plus.induct)
apply(auto)
done

(* global optimazation *)
fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma \<open>aval (asimp a) s = aval a s\<close>
apply(induction a)
apply(auto simp: aval_plus)
done

(* value "True" *)
(* value "True \<and> True" *)

(* Exercise 3.1 *)
fun optimal :: "aexp \<Rightarrow> bool" where
(* base case *)
"optimal (N n) = True" |
"optimal (V x) = True" |
(* top most trivial case *)
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus a1 a2) = ((optimal a1) \<and> (optimal a2))"

lemma \<open>optimal (asimp_const a)\<close>
apply(induction a)
apply(auto split: aexp.split)
done

(* Exercise 3.2 *)
(* Use case *)
(* full_asimp (Plus (N 1) (Plus (V x) (N 2))) = Plus (V x) (N 3) *)

(* local optimization for full_asimp *)
fun full_plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"full_plus (N i1) (N i2) = N (i1 + i2)" |
"full_plus (N i1) (Plus a (N i2)) = Plus a (N (i1 + i2))" |
"full_plus (Plus a (N i1)) (N i2) = Plus a (N (i1 + i2))" |
"full_plus (N i) a = (if i=0 then a else Plus a (N i))" |
"full_plus a (N i) = (if i=0 then a else Plus a (N i))" |
"full_plus a1 a2 = Plus a1 a2"
(* global optimization *)
fun full_asimp :: "aexp \<Rightarrow> aexp" where
(* base case *)
"full_asimp (N n) = N n" |
"full_asimp (V x) = V x" |
(* recursive case, i.e wishful thinking *)
"full_asimp (Plus a1 a2) = full_plus (full_asimp a1) (full_asimp a2)"

lemma aval_full_plus: "aval (full_plus a1 a2) s = aval a1 s + aval a2 s"
apply(induction rule: full_plus.induct)
apply(auto)
done

lemma \<open>aval (full_asimp a) s = aval a s\<close>
apply(induction a)
apply(auto simp: aval_full_plus)
done

(* test case *)
(* full_asimp (Plus (N 1) (Plus (V x) (N 2))) = Plus (V x) (N 3) *)
lemma \<open>full_asimp (Plus (N 1) (Plus (V x) (N 2))) = Plus (V x) (N 3)\<close>
apply(auto)
done

(* Exercise 3.3 *)

(* Use case *)
(* subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'') *)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
(* base case *)
"subst x a (N n) = N n" |
"subst x a (V y) = (if x=y then a else (V y))" |
"subst x a (Plus e1 e2) = Plus (subst x a e1) (subst x a e2)"

(* test *)
value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')"

lemma substitution_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
apply(induction e)
apply(auto)
done

corollary "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
apply(auto simp: substitution_lemma)
done