theory embedding_frames
  imports embedding_shallow
begin

(*we introduce some default modalities and constraints*)
consts \<R>::"w\<Rightarrow>\<sigma>"  (*binary accessibility relation*)
consts \<T>::"w\<Rightarrow>(w\<Rightarrow>\<sigma>)"  (*ternary accessibility relation*)
(*for multi-modal logics we can provide the accessibility relation as a parameter*)

definition box::"\<sigma>\<Rightarrow>\<sigma>" ("\<box>_" [57]58) where "\<box>A \<equiv> \<lambda>w. \<forall>v. \<R> w v \<longrightarrow> A v"
definition dia::"\<sigma>\<Rightarrow>\<sigma>" ("\<diamond>_" [57]58) where "\<diamond>A \<equiv> \<lambda>w. \<exists>v. \<R> w v \<and>  A v"
definition fusion::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<otimes>" 80) where "A \<otimes> B \<equiv> \<lambda>x. (\<exists>y z. (\<T> y z x \<and> A y) \<and> B z)"
definition impl::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<Rightarrow>" 80) where "A \<Rightarrow> B \<equiv> \<lambda>x. (\<forall>y z. (\<T> y x z \<and> A y) \<longrightarrow> B z)"
definition lpmi::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<Leftarrow>" 80) where "B \<Leftarrow> A \<equiv> \<lambda>x. (\<forall>y z. (\<T> x y z \<and> A y) \<longrightarrow> B z)"

lemma assoc: "(A \<otimes> (B \<otimes> C)) = ((A \<otimes> B) \<otimes> C)" nitpick oops (*non assoc*)
lemma exchange: "(A \<otimes> B) = (B \<otimes> A)" nitpick oops  (*non comm*)
lemma contraction: "(A \<otimes> A) = A" nitpick oops (*non idem*)
lemma lw: "(A \<otimes> B) \<subseteq> A" nitpick oops

lemma "A \<otimes> (A \<Rightarrow> B) \<subseteq> B" using impl_def fusion_def subset_def by fastforce
lemma "B \<subseteq> A \<Rightarrow> (A \<otimes> B)" using impl_def fusion_def subset_def by fastforce
lemma "(B \<Leftarrow> A) \<otimes> A \<subseteq> B" using fusion_def lpmi_def subset_def by fastforce

lemma "A \<subseteq> B \<and> C \<subseteq> D \<longrightarrow> A \<otimes> C \<subseteq> B \<otimes> D" by (smt (verit, del_insts) fusion_def subset_def)
lemma "A \<subseteq> B \<and> C \<subseteq> D \<longrightarrow> B \<Rightarrow> C \<subseteq> A \<Rightarrow> D" by (smt (verit, ccfv_SIG) impl_def subset_def)
lemma "A \<subseteq> B \<and> C \<subseteq> D \<longrightarrow> C \<Leftarrow> B \<subseteq> D \<Leftarrow> A" by (smt (verit, best) lpmi_def subset_def)

(*We can say of two unary operators \<phi> and \<psi> that they form an "adjoint" or "residuated" pair.
 We then call \<phi> (\<psi>) the down (up) adjoint/residue to/of \<psi> (\<phi>).*)
definition Residuated::"\<sigma> Rel \<Rightarrow> (\<sigma>\<Rightarrow>\<sigma>)Rel" ("_-RESID")
  where "R-RESID \<phi> \<psi> \<equiv> \<forall>A B. R (\<phi> A) B \<longleftrightarrow> R A (\<psi> B)"

(*We can express residuation for binary operators in two different flavours*)
abbreviation Residuated_left::"\<sigma> Rel \<Rightarrow> (\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>)Rel" ("_-RESID\<^sup>l")
  where "R-RESID\<^sup>l \<phi> \<psi> \<equiv> \<forall>A. R-RESID (\<phi> A) (\<psi> A)"
abbreviation Residuated_right::"\<sigma> Rel \<Rightarrow> (\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>)Rel" ("_-RESID\<^sup>r")
  where "R-RESID\<^sup>r \<phi> \<psi> \<equiv> \<forall>A. R-RESID (\<phi>\<^sup>T A) (\<psi>\<^sup>T A)"

lemma "R-RESID\<^sup>l \<phi> \<psi> = (\<forall>A B C. R (\<phi> A B) C \<longleftrightarrow> R B (\<psi> A C))" unfolding Residuated_def by simp
lemma "R-RESID\<^sup>r \<phi> \<psi> = (\<forall>A B C. R (\<phi> B A) C \<longleftrightarrow> R B (\<psi> C A))" unfolding Residuated_def by simp


(*For instance*)
lemma "(\<preceq>)-RESID\<^sup>l (\<inter>) (\<rightarrow>) \<longleftrightarrow> (A \<inter> B \<preceq> C \<longleftrightarrow> B \<preceq> A \<rightarrow> C)" by (smt (verit, best) Residuated_def base.impl_def inter_def subset_def)
lemma "(\<preceq>)-RESID\<^sup>r (\<leftharpoonup>) (\<union>) \<longleftrightarrow> (B \<leftharpoonup> A \<preceq> C \<longleftrightarrow> B \<preceq> C \<union> A)" by (smt (verit) Residuated_def diff_def subset_def union_def)

(*We have in fact*)
lemma "(\<preceq>)-RESID\<^sup>l (\<inter>) (\<rightarrow>)" by (smt (verit, ccfv_SIG) Residuated_def base.impl_def inter_def subset_def)
lemma "(\<preceq>)-RESID\<^sup>r (\<leftharpoonup>) (\<union>)" by (smt (verit, best) Residuated_def diff_def subset_def union_def)
(*And also*)
lemma "(\<preceq>)-RESID\<^sup>l (\<otimes>) (\<Rightarrow>)" by (smt (z3) Residuated_def impl_def fusion_def subset_def)
lemma "(\<preceq>)-RESID\<^sup>r (\<otimes>) (\<Leftarrow>)" by (smt (z3) Residuated_def fusion_def lpmi_def subset_def)

lemma "(\<Leftarrow>) = (\<Rightarrow>)\<^sup>T" nitpick oops

axiomatization 
  where assoc\<T>: "\<forall>x y z u. (\<exists>s. \<T> x y s \<and> \<T> s z u) \<longleftrightarrow> (\<exists>t. \<T> x t u \<and> \<T> y z t) "

lemma assoc: "(A \<otimes> (B \<otimes> C)) = ((A \<otimes> B) \<otimes> C)" unfolding fusion_def using assoc\<T> by fastforce (*assoc*)

axiomatization 
  where comm\<T>: "\<forall>x y u. \<T> x y u \<longleftrightarrow> (\<T> y x u) "

lemma exchange: "(A \<otimes> B) = (B \<otimes> A)" unfolding fusion_def by (meson comm\<T>)
lemma "(\<preceq>)-RESID\<^sup>r (\<otimes>) (\<Leftarrow>)" by (smt (z3) Residuated_def fusion_def lpmi_def subset_def)
lemma "(\<Leftarrow>) = (\<Rightarrow>)\<^sup>T" using comm\<T> impl_def lpmi_def by presburger
  
lemma contraction1: "(A \<otimes> A) \<subseteq> A" nitpick oops
lemma contraction2: "A  \<subseteq> (A \<otimes> A)" nitpick oops
lemma lw: "(A \<otimes> B) \<subseteq> A" nitpick oops

definition par::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<oplus>" 79) where "A \<oplus> B \<equiv> \<midarrow>(\<midarrow>A \<otimes> \<midarrow>B)"
lemma "A \<otimes> \<midarrow>A \<approx> \<emptyset>" nitpick oops
lemma "A \<oplus> \<midarrow>A \<approx> \<UU>" nitpick oops

end