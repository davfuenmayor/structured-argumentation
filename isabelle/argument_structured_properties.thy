theory argument_structured_properties
  imports argument_structured extensions
begin

(*We now examine different preservation properties of our algebra of arguments*)

(*We start by conveniently extending our two FOUR-solvers for working with arguments*)
method s1A = unfold defends_def argDefs1 connSet connArg1; s1
method s2A = unfold defends_def argDefs2 connSet connArg1; s2

(********** Deductiveness  **********)
lemma "\<D> a \<and> \<D> b \<longrightarrow> \<D>(a \<sqinter>\<^sup>a b)" by s1A (*s2A*)
lemma "\<D> a \<and> \<D> b \<longrightarrow> \<D>(a \<squnion>\<^sup>a b)" by s1A (*s2A*)
lemma "\<D> A \<and> A \<sqsubseteq>\<^sup>a B \<longrightarrow> \<D> B" nitpick oops
lemma "\<D> B \<and> A \<sqsubseteq>\<^sup>a B \<longrightarrow> \<D> A" nitpick oops
lemma "\<D>(a \<sqinter>\<^sup>a b) \<longrightarrow> (\<D> a \<or> \<D> b)" nitpick oops
lemma "\<D>(a \<squnion>\<^sup>a b) \<longrightarrow> (\<D> a \<or> \<D> b)" nitpick oops

lemma "\<D> A \<and> A \<preceq>\<^sup>a B \<longrightarrow> \<D> B" by s1A (*s2A*) 
lemma "\<D>(a \<and>\<^sup>a b) \<longrightarrow> (\<D> a \<and> \<D> b)" by s1A (*s2A*)
lemma "\<D> a \<longrightarrow> \<D>(a \<or>\<^sup>a b)" by s1A (*s2A*)
lemma "\<D> a \<and> \<D> b \<longrightarrow> \<D>(a \<and>\<^sup>a b)" nitpick oops
lemma "\<D>(a \<or>\<^sup>a b) \<longrightarrow> (\<D> a \<or> \<D> b)" nitpick oops

(********** Consistency  **********)
lemma "\<C> A \<and> A \<sqsubseteq>\<^sup>a B \<longrightarrow> \<C> B" by s1A (*s2A*)
lemma "\<C>(a \<sqinter>\<^sup>a b) \<longrightarrow> (\<C> a \<and> \<C> b)" by s1A (*s2A*)
lemma "\<C> a \<longrightarrow> \<C>(a \<squnion>\<^sup>a b)" by s1A (*s2A*)
lemma "\<C> a \<and> \<C> b \<longrightarrow> \<C>(a \<sqinter>\<^sup>a b)" nitpick oops
lemma "\<C>(a \<squnion>\<^sup>a b) \<longrightarrow> (\<C> a \<or> \<C> b)" nitpick oops

lemma "\<C> a \<and> \<C> b \<longrightarrow> \<C>(a \<and>\<^sup>a b)" nitpick oops
lemma "\<C> a \<and> \<C> b \<longrightarrow> \<C>(a \<or>\<^sup>a b)" nitpick oops
lemma "\<C> A \<and> A \<preceq>\<^sup>a B \<longrightarrow> \<C> B" nitpick oops
lemma "\<C> B \<and> A \<preceq>\<^sup>a B \<longrightarrow> \<C> A" nitpick oops
lemma "\<C>(a \<and>\<^sup>a b) \<longrightarrow> (\<C> a \<or> \<C> b)" by s1A (*s2A*)
lemma "\<C>(a \<or>\<^sup>a b) \<longrightarrow> (\<C> a \<or> \<C> b)" by s1A (*s2A*)

(********** Premise-Consistency  **********)
lemma "\<C>' A \<and> A \<sqsubseteq>\<^sup>a B \<longrightarrow> \<C>' B" by s1A (*s2A*)
lemma "\<C>'(a \<sqinter>\<^sup>a b) \<longrightarrow> (\<C>' a \<and> \<C>' b)" by s1A (*s2A*)
lemma "\<C>' a \<longrightarrow> \<C>'(a \<squnion>\<^sup>a b)" by s1A (*s2A*)
lemma "\<C>' a \<and> \<C>' b \<longrightarrow> \<C>'(a \<sqinter>\<^sup>a b)" nitpick oops
lemma "\<C>'(a \<squnion>\<^sup>a b) \<longrightarrow> (\<C>' a \<or> \<C>' b)" by s1A (*s2A*)

lemma "\<C>' B \<and> A \<preceq>\<^sup>a B \<longrightarrow> \<C>' A" by s1A (*s2A*)
lemma "\<C>'(a \<or>\<^sup>a b) \<longrightarrow> (\<C>' a \<and> \<C>' b)" by s1A (*s2A*)
lemma "\<C>' a \<longrightarrow> \<C>'(a \<and>\<^sup>a b)" by s1A (*s2A*)
lemma "\<C>'(a \<and>\<^sup>a b) \<longrightarrow> (\<C>' a \<or> \<C>' b)" by s1A (*s2A*)
lemma "\<C>' a \<and> \<C>' b \<longrightarrow> \<C>'(a \<or>\<^sup>a b)" nitpick oops

(********** Valid *****)
lemma "\<V> A \<and> A \<sqsubseteq>\<^sup>a B \<longrightarrow> \<V> B" nitpick oops
lemma "\<V> B \<and> A \<sqsubseteq>\<^sup>a B \<longrightarrow> \<V> A" nitpick oops
lemma "\<V> a \<and> \<V> b \<longrightarrow> \<V>(a \<squnion>\<^sup>a b)" by s1A
lemma "\<V> a \<and> \<V> b \<longrightarrow> \<V>(a \<sqinter>\<^sup>a b)" nitpick oops
lemma "\<V>(a \<squnion>\<^sup>a b) \<longrightarrow> (\<V> a \<or> \<V> b)" nitpick oops
lemma "\<V>(a \<sqinter>\<^sup>a b) \<longrightarrow> (\<V> a \<or> \<V> b)" nitpick oops

lemma "\<V> A \<and> A \<preceq>\<^sup>a B \<longrightarrow> \<V> B" nitpick oops
lemma "\<V> B \<and> A \<preceq>\<^sup>a B \<longrightarrow> \<V> A" nitpick oops
lemma "\<V> a \<and> \<V> b \<longrightarrow> \<V>(a \<or>\<^sup>a b)" nitpick oops
lemma "\<V> a \<and> \<V> b \<longrightarrow> \<V>(a \<and>\<^sup>a b)" nitpick oops
lemma "\<V>(a \<or>\<^sup>a b) \<longrightarrow> (\<V> a \<or> \<V> b)" nitpick oops
lemma "\<V>(a \<and>\<^sup>a b) \<longrightarrow> (\<V> a \<or> \<V> b)" by s1A

(*************** Undermining Attacks ****************)

lemma "undermine a c \<longrightarrow> undermine (a \<sqinter>\<^sup>a b) c" by s1A (*s2A*)
(* lemma "undermine (a \<sqinter>\<^sup>a b) c \<longrightarrow> undermine a c" nitpick oops *)
lemma "undermine a c \<longrightarrow> undermine a (c \<sqinter>\<^sup>a b)" by s1A (*s2A*)
(* lemma "undermine a (c \<sqinter>\<^sup>a b) \<longrightarrow> undermine a c" nitpick oops *)

lemma "undermine (a \<squnion>\<^sup>a b) c \<longrightarrow> undermine a c" by s1A (*s2A*)
(* lemma "undermine a c \<longrightarrow> undermine (a \<squnion>\<^sup>a b) c" nitpick oops *)
lemma "undermine a (c \<squnion>\<^sup>a b) \<longrightarrow> undermine a c" by s1A (*s2A*)
(* lemma "undermine a c \<longrightarrow> undermine a (c \<squnion>\<^sup>a b)" nitpick oops *)

lemma "undermine a c \<longrightarrow> undermine (a \<and>\<^sup>a b) c" by s1A (*s2A*)
(* lemma "undermine (a \<and>\<^sup>a b) c \<longrightarrow> undermine a c" nitpick oops *)
(* lemma "undermine a c \<longrightarrow> undermine a (c \<and>\<^sup>a b)" nitpick oops *)
lemma "undermine a (c \<and>\<^sup>a b) \<longrightarrow> undermine a c" by s1A (*s2A*)

lemma "undermine (a \<or>\<^sup>a b) c \<longrightarrow> undermine a c" by s1A (*s2A*)
(* lemma "undermine a c \<longrightarrow> undermine (a \<or>\<^sup>a b) c" nitpick oops *)
(* lemma "undermine a (c \<or>\<^sup>a b) \<longrightarrow> undermine a c" nitpick oops *)
lemma "undermine a c \<longrightarrow> undermine a (c \<or>\<^sup>a b)" by s1A (*s2A*)


(*************** Rebutting Attacks ****************)

lemma "rebute a c \<longrightarrow> rebute (a \<sqinter>\<^sup>a b) c" by s1A (*s2A*)
lemma "rebute (a \<sqinter>\<^sup>a b) c \<longrightarrow> rebute a c" nitpick oops
lemma "rebute a c \<longrightarrow> rebute a (c \<sqinter>\<^sup>a b)" by s1A (*s2A*)
lemma "rebute a (c \<sqinter>\<^sup>a b) \<longrightarrow> rebute a c" nitpick oops

lemma "rebute (a \<squnion>\<^sup>a b) c \<longrightarrow> rebute a c" by s1A (*s2A*)
lemma "rebute a c \<longrightarrow> rebute (a \<squnion>\<^sup>a b) c" nitpick oops
lemma "rebute a (c \<squnion>\<^sup>a b) \<longrightarrow> rebute a c" by s1A (*s2A*)
lemma "rebute a c \<longrightarrow> rebute a (c \<squnion>\<^sup>a b)" nitpick oops

lemma "rebute a c \<longrightarrow> rebute (a \<and>\<^sup>a b) c" by s1A (*s2A*)
lemma "rebute (a \<and>\<^sup>a b) c \<longrightarrow> rebute a c" nitpick oops
lemma "rebute a c \<longrightarrow> rebute a (c \<and>\<^sup>a b)" by s1A (*s2A*)
lemma "rebute a (c \<and>\<^sup>a b) \<longrightarrow> rebute a c" nitpick oops

lemma "rebute (a \<or>\<^sup>a b) c \<longrightarrow> rebute a c" by s1A (*s2A*)
lemma "rebute a c \<longrightarrow> rebute (a \<or>\<^sup>a b) c" nitpick oops
lemma "rebute a (c \<or>\<^sup>a b) \<longrightarrow> rebute a c" by s1A (*s2A*)
lemma "rebute a c \<longrightarrow> rebute a (c \<or>\<^sup>a b)" nitpick oops

(*************** Undercutting Attacks ****************)

lemma "undercut a c \<longrightarrow> undercut (a \<sqinter>\<^sup>a b) c" by s1A (*s2A*)
lemma "undercut (a \<sqinter>\<^sup>a b) c \<longrightarrow> undercut a c" nitpick oops
lemma "undercut a c \<longrightarrow> undercut a (c \<sqinter>\<^sup>a b)" nitpick oops
lemma "undercut a (c \<sqinter>\<^sup>a b) \<longrightarrow> undercut a c" nitpick oops

lemma "undercut (a \<squnion>\<^sup>a b) c \<longrightarrow> undercut a c" by s1A (*s2A*)
lemma "undercut a c \<longrightarrow> undercut (a \<squnion>\<^sup>a b) c" nitpick oops
lemma "undercut a (c \<squnion>\<^sup>a b) \<longrightarrow> undercut a c" nitpick oops
lemma "undercut a c \<longrightarrow> undercut a (c \<squnion>\<^sup>a b)" nitpick oops

lemma "undercut a c \<longrightarrow> undercut (a \<and>\<^sup>a b) c" by s1A (*s2A*)
lemma "undercut (a \<and>\<^sup>a b) c \<longrightarrow> undercut a c" nitpick oops
lemma "undercut a c \<longrightarrow> undercut a (c \<and>\<^sup>a b)" by s1A (*s2A*)
lemma "undercut a (c \<and>\<^sup>a b) \<longrightarrow> undercut a c" nitpick oops

lemma "undercut (a \<or>\<^sup>a b) c \<longrightarrow> undercut a c" by s1A (*s2A*)
lemma "undercut a c \<longrightarrow> undercut (a \<or>\<^sup>a b) c" nitpick oops
lemma "undercut a (c \<or>\<^sup>a b) \<longrightarrow> undercut a c" by s1A (*s2A*)
lemma "undercut a c \<longrightarrow> undercut a (c \<or>\<^sup>a b)" nitpick oops


(******************** Defence ****************)

(* A set is closed under a given binary operation*)
abbreviation closedUnder ("_-closed")
  where "f-closed S \<equiv> \<forall>a b. S a \<and> S b \<longrightarrow> S (f a b)"

locale TestDefence =
  fixes \<A>::"\<alpha> Set" and a::\<alpha> and b::\<alpha> and c::\<alpha>
  assumes ax: "\<A> a \<and> \<A> b \<and> \<A> c" 
begin

lemma "defends\<^sup>\<A> undermine\<^sup>\<A> S b \<longrightarrow> defends\<^sup>\<A> undermine\<^sup>\<A> S (b \<squnion>\<^sup>a c)" using ax by s1A (*s2A*)
lemma "(\<sqinter>\<^sup>a)-closed \<A> \<Longrightarrow> defends\<^sup>\<A> undermine\<^sup>\<A> S (b \<sqinter>\<^sup>a c) \<longrightarrow> defends\<^sup>\<A> undermine\<^sup>\<A> S b \<and> defends\<^sup>\<A> undermine\<^sup>\<A> S c" using ax by s1A

lemma "defends\<^sup>\<A> rebute\<^sup>\<A> S b \<longrightarrow> defends\<^sup>\<A> rebute\<^sup>\<A> S (b \<or>\<^sup>a c)" using ax by s1A (*s2A*)
lemma "(\<and>\<^sup>a)-closed \<A> \<Longrightarrow> defends\<^sup>\<A> rebute\<^sup>\<A> S (b \<and>\<^sup>a c) \<longrightarrow> defends\<^sup>\<A> rebute\<^sup>\<A> S b \<and> defends\<^sup>\<A> rebute\<^sup>\<A> S c" using ax by s1A

lemma "defends\<^sup>\<A> undercut\<^sup>\<A> S b \<longrightarrow> defends\<^sup>\<A> undercut\<^sup>\<A> S (b \<squnion>\<^sup>a c)" using ax apply s1A by blast
lemma "(\<sqinter>\<^sup>a)-closed \<A> \<Longrightarrow> defends\<^sup>\<A> undercut\<^sup>\<A> S (b \<sqinter>\<^sup>a c) \<longrightarrow> defends\<^sup>\<A> undercut\<^sup>\<A> S b \<and> defends\<^sup>\<A> undercut\<^sup>\<A> S c" using ax apply s1A by (smt (verit, del_insts))+ (* takes some time *)
lemma "defends\<^sup>\<A> undercut\<^sup>\<A> S b \<longrightarrow> defends\<^sup>\<A> undercut\<^sup>\<A> S (b \<or>\<^sup>a c)" using ax by s1A (*s2A*)
lemma "(\<and>\<^sup>a)-closed \<A> \<Longrightarrow> defends\<^sup>\<A> undercut\<^sup>\<A> S (b \<and>\<^sup>a c) \<longrightarrow> defends\<^sup>\<A> undercut\<^sup>\<A> S b \<and> defends\<^sup>\<A> undercut\<^sup>\<A> S c" using ax by s1A 
end

(******************** Closure under complete extensions ****************)

lemma "(\<squnion>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> undermine\<^sup>\<A> S) \<longrightarrow> (\<squnion>\<^sup>a)-closed S" 
  unfolding completeExt_def2 by s2A
lemma "(\<squnion>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> rebute\<^sup>\<A> S) \<longrightarrow> (\<squnion>\<^sup>a)-closed S"
  unfolding completeExt_def2 by s2A
lemma "(\<squnion>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> undercut\<^sup>\<A> S) \<longrightarrow> (\<squnion>\<^sup>a)-closed S" 
  unfolding completeExt_def2 undercut_def eqset_rel_def2 by s2A

lemma "(\<or>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> undermine\<^sup>\<A> S) \<longrightarrow> (\<or>\<^sup>a)-closed S"
  nitpick oops 
lemma "(\<or>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> rebute\<^sup>\<A> S) \<longrightarrow> (\<or>\<^sup>a)-closed S"
  unfolding completeExt_def2 by s2A
lemma "(\<or>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> undercut\<^sup>\<A> S) \<longrightarrow> (\<or>\<^sup>a)-closed S" 
  unfolding completeExt_def2 undercut_def eqset_rel_def2 by s2A

lemma "(\<sqinter>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> undermine\<^sup>\<A> S) \<longrightarrow> (\<sqinter>\<^sup>a)-closed S" 
  nitpick oops
lemma "(\<sqinter>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> rebute\<^sup>\<A> S) \<longrightarrow> (\<sqinter>\<^sup>a)-closed S"
  nitpick oops 
lemma "(\<sqinter>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> undercut\<^sup>\<A> S) \<longrightarrow> (\<sqinter>\<^sup>a)-closed S"
  unfolding completeExt_def2 undercut_def eqset_rel_def2 by s2A

lemma "(\<and>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> undermine\<^sup>\<A> S) \<longrightarrow> (\<and>\<^sup>a)-closed S" 
  unfolding completeExt_def2 by s2A
lemma "(\<and>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> rebute\<^sup>\<A> S) \<longrightarrow> (\<and>\<^sup>a)-closed S"
  nitpick oops 
lemma "(\<and>\<^sup>a)-closed \<A> \<and> S \<subseteq> \<A> \<Longrightarrow> (completeExt\<^sup>\<A> undercut\<^sup>\<A> S) \<longrightarrow> (\<and>\<^sup>a)-closed S"
  oops (*TODO reconstruct*)

end