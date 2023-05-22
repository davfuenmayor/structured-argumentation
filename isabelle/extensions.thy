theory extensions
  imports base 
begin

named_theorems extDefs

subsection \<open>Defends\<close>

(*The set of elements (e.g. arguments) that the set S defends (wrt. 'attack' relation R)*)
definition defends :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("defends\<^sup>_")
  where \<open>defends\<^sup>\<A> \<equiv> \<lambda>R S a. \<forall>b. \<A> b \<longrightarrow> R b a \<longrightarrow> (\<exists>z. \<A> z \<and> S z \<and> R z b)\<close>

(* The function 'defends' corresponds to the so-called 'characteristic function'
   in the literature of an argumentation frameworks (e.g. [BCG 2011] Def. 11). *)

(* 'defends' is monotone (i.e. order preserving wrt. set inclusion). *)
lemma defends_mono': "MONO (defends\<^sup>\<A> R)" unfolding MONO_def by (smt (verit) defends_def subset_def)
lemma defends_mono: "MONO\<^sup>\<A> (defends\<^sup>\<A> R)" unfolding MONO_rel_def defends_def by (smt (verit) subset_rel_def)

(* We can now verify that 'defends' has both a least and a greatest fixed point (in different formulations). *)
lemma defends_leastFP': \<open>\<exists>S. (\<subseteq>)-least (fp (defends\<^sup>\<A> R)) S\<close> by (simp add: defends_mono' wKTl)
lemma defends_greatestFP': \<open>\<exists>S. (\<subseteq>)-greatest (fp (defends\<^sup>\<A> R)) S\<close> by (simp add: defends_mono' wKTg)

(*Some syntactic sugar for max/min & least/greatest wrt. relativized subset relation*)
abbreviation max_rel ("'(\<subseteq>\<^sub>_')-max") where "max_rel A \<equiv> maximal (\<lambda>X Y. X \<subseteq>\<^sub>A Y)"
abbreviation min_rel ("'(\<subseteq>\<^sub>_')-min") where "min_rel A \<equiv> minimal (\<lambda>X Y. X \<subseteq>\<^sub>A Y)"
abbreviation least_rel ("'(\<subseteq>\<^sub>_')-least") where "least_rel A \<equiv> least (\<lambda>X Y. X \<subseteq>\<^sub>A Y)"
abbreviation greatest_rel ("'(\<subseteq>\<^sub>_')-greatest") where "greatest_rel A \<equiv> greatest (\<lambda>X Y. X \<subseteq>\<^sub>A Y)"

lemma defends_leastFP:  \<open>\<exists>S. (\<subseteq>\<^sub>\<A>)-least (fp\<^sup>\<A> (defends\<^sup>\<A> R)) S\<close> by (simp add: defends_mono wKTl_relw)
lemma defends_greatestFP:  \<open>\<exists>S. (\<subseteq>\<^sub>\<A>)-greatest (fp\<^sup>\<A> (defends\<^sup>\<A> R)) S\<close> by (simp add: defends_mono wKTg_relw)


subsection \<open>Basic Principles\<close>

(* A set S of arguments is said to be conflict-free if there are no arguments A and B in S 
  such that A attacks B ([Dung 1995] Def. 5 and [BCG 2011] Def. 12). *)
definition conflictfree :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a Set)Set\<close> ("conflictfree\<^sup>_")
  where \<open>conflictfree\<^sup>\<A> \<equiv> \<lambda>att S. \<forall>a b. (\<A> a \<and> \<A> b) \<longrightarrow> (S a \<and> S b) \<longrightarrow> \<not>(att a b)\<close>

(* A set of arguments S is admissible if it is conflict-free and each argument in S is
  defended by S ([Dung 1995] Def. 6(2) and [BCG 2011] Def. 13). *)
definition admissible :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a Set)Set\<close> ("admissible\<^sup>_")
  where \<open>admissible\<^sup>\<A> \<equiv> \<lambda>att S. conflictfree\<^sup>\<A> att S \<and> (\<forall>a. \<A> a \<longrightarrow> S a \<longrightarrow> defends\<^sup>\<A> att S a)\<close>


subsection \<open>Extension-based Semantics\<close>

(***********************************************************)
(* Complete extensions.                                    *)
(***********************************************************)

(* An admissible set S of arguments is called a complete extension if each argument,
  which is defended by S, belongs to S ([Dung 1995] Def. 23). *)
definition completeExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a Set)Set\<close> ("completeExt\<^sup>_")
  where \<open>completeExt\<^sup>\<A> \<equiv> \<lambda>att S. admissible\<^sup>\<A> att S \<and> (\<forall>a. \<A> a \<longrightarrow> defends\<^sup>\<A> att S a \<longrightarrow> S a)\<close>

(* Alternatively, complete extensions can be defined as conflict-free fixed points of defends (see [Dung 1995] Lemma 24)*)
lemma completeExt_def2: \<open>completeExt\<^sup>\<A> = (\<lambda>att S. conflictfree\<^sup>\<A> att S \<and> fp\<^sup>\<A> (defends\<^sup>\<A> att) S)\<close>
  unfolding admissible_def completeExt_def eqset_rel_def2 subset_rel_def by blast

(* The grounded extension of an argumentation framework AF is a minimal complete extension ([BCG 2011] Def. 21). *)
definition groundedExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a Set)Set\<close> ("groundedExt\<^sup>_")
  where \<open>groundedExt\<^sup>\<A> \<equiv> \<lambda>att S. (\<subseteq>\<^sub>\<A>)-min (completeExt\<^sup>\<A> att) S\<close>

(* Alternatively, grounded extensions can be defined as least complete extensions*)
lemma groundedExt_def2: \<open>groundedExt\<^sup>\<A> = (\<lambda>att S. (\<subseteq>\<^sub>\<A>)-least (completeExt\<^sup>\<A> att) S)\<close>
  unfolding groundedExt_def completeExt_def2 using defends_leastFP oops (*TODO prove*)

(* Alternatively, according to Dung, the grounded extension of an argumentation framework AF is
   the least fixed point of defends ([Dung 1995] Def. 20). *)
lemma groundedExt_def3: \<open>groundedExt\<^sup>\<A> = (\<lambda>att S. (\<subseteq>\<^sub>\<A>)-least (fp\<^sup>\<A> (defends\<^sup>\<A> att)) S)\<close>
  oops (*TODO prove*)

(* A preferred extension of an argumentation framework AF is a maximal (with respect to set inclusion)
  complete extension of AF. *)
definition preferredExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a Set)Set\<close> ("preferredExt\<^sup>_")
  where \<open>preferredExt\<^sup>\<A> \<equiv> \<lambda>att S. (\<subseteq>\<^sub>\<A>)-max (completeExt\<^sup>\<A> att) S\<close>

(* Alternatively, preferred extensions can be defined as maximal admissible sets ([Dung 1995] Def. 7)*)
lemma preferredExt_def2: \<open>preferredExt\<^sup>\<A> = (\<lambda>att S. (\<subseteq>\<^sub>\<A>)-max (admissible\<^sup>\<A> att) S)\<close>
  oops (*TODO prove*)

(***********************************************************)
(* Ideal extensions.                                       *)
(***********************************************************)

(* An ideal set is an admissible set that is subset of every preferred extension*)
definition idealSet :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a Set)Set\<close> ("idealSet\<^sup>_")
  where \<open>idealSet\<^sup>\<A> \<equiv> \<lambda>att S. admissible\<^sup>\<A> att S \<and> (\<forall>E. preferredExt\<^sup>\<A> att E \<longrightarrow> S \<subseteq>\<^sub>\<A> E)\<close>

(* An ideal extension of an argumentation framework AF is the (unique) 
  maximal (i.e greatest) ideal set. ([BCG 2011] Def. 30 and paragraph below). *)
definition idealExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a Set)Set\<close> ("idealExt\<^sup>_")
  where \<open>idealExt\<^sup>\<A> \<equiv> \<lambda>att S. (\<subseteq>\<^sub>\<A>)-greatest (idealSet\<^sup>\<A> att) S\<close>

(*or alternatively*)
lemma idealExt_def2: \<open>idealExt\<^sup>\<A> = (\<lambda>att S. (\<subseteq>\<^sub>\<A>)-max (idealSet\<^sup>\<A> att) S)\<close>
  oops (*TODO prove*)

(***********************************************************)
(* Stable extensions.                                      *)
(***********************************************************)

(* We define the range of a set of arguments S as the union of S with the set 
  of its attacked arguments. *)
definition range :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("range\<^sup>_")
  where \<open>range\<^sup>\<A> att \<equiv> \<lambda>S. S \<union> (\<lambda>b. (\<exists>a. \<A> a \<and> S a \<and> att a b))\<close>

(* A stable extension of an argumentation framework AF is a conflict-free extension E
   such that E \<union> E\<^sup>+ = Args ([BCG 2011] Def. 25). *)
definition stableExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a Set)Set\<close> ("stableExt\<^sup>_")
  where \<open>stableExt\<^sup>\<A> \<equiv> \<lambda>att S. (conflictfree\<^sup>\<A> att S) \<and> \<A> \<subseteq> range\<^sup>\<A> att S\<close>

(* A semi-stable extension of an argumentation framework AF is a complete extension E
   such that E \<union> E\<^sup>+ is maximal among all complete extensions. ([BCG 2011] Def. 27). *)
definition semistableExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a Set)Set\<close> ("semistableExt\<^sup>_")
  where \<open>semistableExt\<^sup>\<A> \<equiv> \<lambda>att S. maximal (\<lambda>X Y. (range\<^sup>\<A> att X) \<subseteq>\<^sub>\<A> (range\<^sup>\<A> att Y)) (completeExt\<^sup>\<A> att) S\<close>

(***********************************************************)
(* Stage extensions.                                       *)
(***********************************************************)

(* A stage extension of an argumentation framework AF is a conflict-free extension E
   such that E \<union> E\<^sup>+ is maximal among all conflict-free extensions. ([BCG 2011] Def. 32). *)
definition stageExt :: \<open>'a Set \<Rightarrow> 'a Rel \<Rightarrow> ('a Set)Set\<close> ("stageExt\<^sup>_")
  where \<open>stageExt\<^sup>\<A> \<equiv> \<lambda>att S. maximal (\<lambda>X Y. (range\<^sup>\<A> att X) \<subseteq>\<^sub>\<A> (range\<^sup>\<A> att Y)) (conflictfree\<^sup>\<A> att) S\<close>

end