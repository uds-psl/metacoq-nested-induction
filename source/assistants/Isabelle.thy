theory Ind
imports Main
begin

datatype tree = tC "tree list"
thm tree.induct
(* thm compat_tree.induct *)
(*
(\<And>xa. (\<And>xaa. xaa \<in> set xa \<Longrightarrow> ?P xaa) \<Longrightarrow> ?P (tC xa)) \<Longrightarrow> ?P ?tree
*)

datatype_compat tree
thm tree.induct
thm compat_tree.induct
(*
(\<And>x. ?P2.0 x \<Longrightarrow> ?P1.0 (tC x)) \<Longrightarrow>
?P2.0 [] \<Longrightarrow>
(\<And>x1a x2. ?P1.0 x1a \<Longrightarrow> ?P2.0 x2 \<Longrightarrow> ?P2.0 (x1a # x2)) \<Longrightarrow>
?P1.0 ?tree
*)

datatype 'a list2 =
    Nil2
    | Cons2 'a "'a list2"

 thm list2.induct
(*
?P Nil2 \<Longrightarrow> (\<And>x1 x2. ?P x2 \<Longrightarrow> ?P (Cons2 x1 x2)) \<Longrightarrow> ?P ?list2.0
*)

datatype tree2 = tC2 "tree2 list2"
thm tree2.induct

(*
(\<And>xa. (\<And>xaa. xaa \<in> set_list2 xa \<Longrightarrow> ?P xaa) \<Longrightarrow> ?P (tC2 xa)) \<Longrightarrow> ?P ?tree2.0
*)

datatype 'a D = d0 | d1 'a | d2 "'a D" | dnL "'a list" | dn "('a D) list2"

thm D.induct 
(*
?P d0 \<Longrightarrow>
(\<And>x. ?P (d1 x)) \<Longrightarrow>
(\<And>x. ?P x \<Longrightarrow> ?P (d2 x)) \<Longrightarrow>
(\<And>x. ?P (dnL x)) \<Longrightarrow>
(\<And>x. (\<And>xa. xa \<in> set_list2 x \<Longrightarrow> ?P xa) \<Longrightarrow> ?P (dn x)) \<Longrightarrow> ?P ?D
*)

datatype tree3 = tC2 "tree3 D"
thm tree3.induct
(* set_D *)
(*
(\<And>xa. (\<And>xaa. xaa \<in> set_D xa \<Longrightarrow> ?P xaa) \<Longrightarrow> ?P (tree3.tC2 xa)) \<Longrightarrow> ?P ?tree3.0
*)

datatype 'a btree =
    leaf
    | branch 'a "'a btree" "'a btree"

    thm btree.induct
(*
?P leaf \<Longrightarrow> (\<And>x1 x2 x3. ?P x2 \<Longrightarrow> ?P x3 \<Longrightarrow> ?P (branch x1 x2 x3)) \<Longrightarrow> ?P ?btree
*)

datatype tree4 = tC "tree4 btree"
thm tree4.induct
(* set_btree *)
(*
(\<And>xa. (\<And>xaa. xaa \<in> set_btree xa \<Longrightarrow> ?P xaa) \<Longrightarrow> ?P (tree4.tC xa)) \<Longrightarrow> ?P ?tree4.0
*)

datatype tree5 = tc "tree5 list"
thm tree5.induct
(*
(\<And>xa. (\<And>xaa. xaa \<in> set xa \<Longrightarrow> ?P xaa) \<Longrightarrow> ?P (tc xa)) \<Longrightarrow> ?P ?tree5.0
*)

datatype tree6 = tc "(nat \<Rightarrow> tree6 list)"
thm tree6.induct
(*
(\<And>xa. (\<And>xaa xaaa. xaa \<in> range xa \<Longrightarrow> xaaa \<in> set xaa \<Longrightarrow> ?P xaaa) \<Longrightarrow>
       ?P (tree6.tc xa)) \<Longrightarrow>
?P ?tree6.0
*)

lemma "
(\<And>(f::nat\<Rightarrow>tree6 list).
   (\<And>(tl::tree6 list) (t::tree6). tl \<in> range f \<Longrightarrow> t \<in> set tl \<Longrightarrow> p t)
   \<Longrightarrow>
   p (tree6.tc f)
) \<Longrightarrow>
\<forall>t.  p t"
apply auto
apply(rule tree6.induct[of p])
by simp

datatype tree7 = tb | tc "(nat \<Rightarrow> tree7)"
thm tree7.induct
(*
?P tb \<Longrightarrow> (\<And>x. (\<And>xa. xa \<in> range x \<Longrightarrow> ?P xa) \<Longrightarrow> ?P (tree7.tc x)) \<Longrightarrow> ?P ?tree7.0
*)

lemma "p tb \<Longrightarrow> (\<And>f. (\<And>t. t \<in> range f \<Longrightarrow> p t) \<Longrightarrow> p (tree7.tc f)) \<Longrightarrow> p t"
apply(rule tree7.induct)
by auto

lemma "p tb \<Longrightarrow> (\<And>(f::nat\<Rightarrow>tree7). (\<And>(n::nat). p (f n)) \<Longrightarrow> p (tS f)) \<Longrightarrow> p t"
apply(rule tree7.induct)
apply auto
sorry


datatype 'a G = tc "'a \<Rightarrow> 'a G" | tb
thm G.induct

datatype tree8 = tb | tc "(nat \<Rightarrow> bool \<Rightarrow> tree8)"
thm tree8.induct

end