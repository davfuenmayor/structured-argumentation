theory embedding_basic
  imports base
begin

typedecl w (*type of worlds/states*)
type_synonym \<sigma>="w Set" (*type of propositions qua sets of worlds*)

(**shallow embedding of base classical logical constants*)
abbreviation conj::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<and>" 54) where "A \<^bold>\<and> B \<equiv> A \<inter> B"
abbreviation disj::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<or>" 53) where "A \<^bold>\<or> B \<equiv> A \<union> B"
abbreviation impl::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<rightarrow>" 51) where "A \<^bold>\<rightarrow> B \<equiv> A \<rightarrow> B"
abbreviation compl::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<midarrow>_" [57]58) where "\<^bold>\<midarrow>A  \<equiv> \<midarrow>A"
abbreviation top::"\<sigma>" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<UU>"
abbreviation bot::"\<sigma>" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<emptyset>"

(**propositions' ordering*)
abbreviation order::"\<sigma> Rel" (infixr "\<preceq>" 45) where "A \<preceq> B \<equiv> A \<subseteq> B"

(**definitions regarding logical consequence, satisfiability and truth*)
abbreviation mval::"\<sigma>\<Rightarrow>bool"     ("[\<^bold>\<turnstile> _]")   where   "[\<^bold>\<turnstile>  \<phi>]  \<equiv> \<phi> \<approx> \<^bold>\<top>"
abbreviation munsat::"\<sigma>\<Rightarrow>bool" ("[\<^bold>\<turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t _]") where "[\<^bold>\<turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t \<phi>] \<equiv> \<phi> \<approx> \<^bold>\<bottom>"
abbreviation munsat2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[\<^bold>\<turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t _, _]") where "[\<^bold>\<turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t \<phi>, \<psi>] \<equiv> \<phi> \<^bold>\<and> \<psi> \<approx> \<^bold>\<bottom>"
abbreviation msat::"\<sigma>\<Rightarrow>bool"    ("[\<^bold>\<turnstile>\<^sup>s\<^sup>a\<^sup>t _]") where  "[\<^bold>\<turnstile>\<^sup>s\<^sup>a\<^sup>t  \<phi>] \<equiv> \<not>[\<^bold>\<turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t  \<phi>]"
abbreviation msat2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool"    ("[\<^bold>\<turnstile>\<^sup>s\<^sup>a\<^sup>t _, _]") where  "[\<^bold>\<turnstile>\<^sup>s\<^sup>a\<^sup>t  \<phi>, \<psi>] \<equiv> \<not>[\<^bold>\<turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t  \<phi>, \<psi>]"
abbreviation conseq_local::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_ \<^bold>\<turnstile> _]") where "[\<phi> \<^bold>\<turnstile> \<psi>] \<equiv> \<phi> \<preceq> \<psi>"
abbreviation conseq_global::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_ \<^bold>\<turnstile>\<^sub>g _]") where "[\<phi> \<^bold>\<turnstile>\<^sub>g \<psi>] \<equiv> [\<^bold>\<turnstile> \<phi>] \<longrightarrow> [\<^bold>\<turnstile> \<psi>]"

(**quantification over individuals of any type (exploiting type polymorphism): *)  
abbreviation qforall::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>_" [55]56) where "\<^bold>\<forall>\<pi> \<equiv> \<lambda>w. \<forall>X. (\<pi> X) w"
abbreviation qexists::"('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>_" [55]56) where "\<^bold>\<exists>\<pi> \<equiv> \<lambda>w. \<exists>X. (\<pi> X) w"
(**to improve readability, we introduce for them an useful binder notation.*)
abbreviation mforallB (binder"\<^bold>\<forall>"[55]56) where "\<^bold>\<forall>X. \<pi> X \<equiv> \<^bold>\<forall>\<pi>"
abbreviation mexistsB (binder"\<^bold>\<exists>"[55]56) where "\<^bold>\<exists>X. \<pi> X \<equiv> \<^bold>\<exists>\<pi>"

end