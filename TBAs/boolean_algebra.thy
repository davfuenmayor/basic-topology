theory boolean_algebra
  imports base
begin

section \<open>Boolean algebras\<close>

(**We encode Boolean algebras via their (Stone) representation as algebras of sets.
This means that each element of (the carrier of) the algebra will be a set (of 'points').
Inspired by the 'propositions as sets of worlds' paradigm from modal logic, we will often refer
to points as 'worlds' and to the elements of our Boolean algebras as 'propositions'.*)

(**The elements of our algebra (propositions) are objects of type @{type "'w\<Rightarrow>bool"} (shortened as @{type "'w \<sigma>"}),
thus corresponding to (characteristic functions of) sets of points.
Propositional functions, as the name indicates, are basically anything with a (parametric) type @{type "'e\<Rightarrow>'w \<sigma>"}.*)

(**We utilize a particular convention on the naming of type variables:
Type variable @{type "'w"} is intended for the domain of points (aka. 'worlds').
This way the polymorphic type @{type "'w \<sigma>"} is a type alias for sets of points (i.e. propositions)
encoded as their corresponding characteristic functions.*)

type_synonym 'w \<sigma> = \<open>'w \<Rightarrow> bool\<close> (*type for propositions as (characteristic functions of) sets*)
type_synonym ('e,'w)\<pi> = \<open>'e \<Rightarrow> 'w \<sigma>\<close> (*type for propositional functions*)

(**In the sequel, we introduce the following naming convention for variables:

(i) Latin letters (A, b, M, P, q, X, y, etc.) denote in general propositions (type @{type "'w \<sigma>"});
however, we try to reserve letters D and S to denote sets of propositions (aka. domains/spaces) 
and the letters u, v and w to denote worlds/points.

(ii) Greek letters denote functions on propositions in general.
Propositional functions in general (type @{type "'e \<Rightarrow> 'w \<sigma>"}) are denoted by @{text "\<pi>"}.
We continue to employ the letters @{text "\<phi>"}, @{text "\<psi>"} and @{text "\<eta>"} to denote
unary connectives/operators (type @{type "'w \<sigma> \<Rightarrow> 'w \<sigma>"}); and the letters
@{text "\<xi>"} and @{text "\<delta>"} to denote binary operations (type @{type "'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>"}).*)

subsection \<open>Encoding Boolean operations\<close>

(**Standard inclusion-based order structure on sets.*)
definition subset::"('w \<sigma>,'w \<sigma>)\<rho>" (infixr "\<^bold>\<preceq>" 45) 
  where "A \<^bold>\<preceq> B \<equiv> \<forall>w. (A w) \<longrightarrow> (B w)"
abbreviation superset::"('w \<sigma>,'w \<sigma>)\<rho>" (infixr "\<^bold>\<succeq>" 45) 
  where "B \<^bold>\<succeq> A \<equiv> A \<^bold>\<preceq> B"
definition setequ::"('w \<sigma>,'w \<sigma>)\<rho>" (infixr "\<^bold>\<approx>" 45) 
  where "(\<^bold>\<approx>) \<equiv> (\<^bold>\<preceq>)\<^sup>R"

named_theorems order (*to group together order-related definitions*)
declare setequ_def[order] subset_def[order]

(**These (trivial) lemmas are intended to help automated tools.*)
lemma setequ_char: "\<phi> \<^bold>\<approx> \<psi> \<equiv> \<forall>w. \<phi> w \<longleftrightarrow> \<psi> w" by (smt (verit, ccfv_threshold) setequ_def subset_def)
lemma setequ_equ: "\<phi> \<^bold>\<approx> \<psi> \<equiv> \<phi> = \<psi>"  proof - (*why so complicated?*)
  have lr: "\<phi> \<^bold>\<approx> \<psi> \<Longrightarrow> \<phi> = \<psi>" unfolding setequ_char by auto
  have rl: "\<phi> = \<psi> \<Longrightarrow> \<phi> \<^bold>\<approx> \<psi>" unfolding setequ_char by simp
  from lr rl show "\<phi> \<^bold>\<approx> \<psi> \<equiv> \<phi> = \<psi>" by linarith
qed

(**We verify that @{text "\<^bold>\<preceq>"} is a preorder and @{text "\<^bold>\<approx>"} is an equivalence relation.*)
lemma subset_reflexive: "reflexive (\<^bold>\<preceq>)" by (simp add: reflexive_def subset_def)
lemma subset_transitive: "transitive (\<^bold>\<preceq>)" by (simp add: transitive_def subset_def)
lemma subset_antisymmetric: "antisymmetric (\<^bold>\<preceq>)" by (metis antisymmetric_def setequ_def setequ_equ)
lemma setequ_reflexive: "reflexive (\<^bold>\<approx>)" by (simp add: reflexive_def setequ_equ)
lemma setequ_transitive: "transitive (\<^bold>\<approx>)" by (simp add: transitive_def setequ_equ)
lemma setequ_symmetric: "symmetric (\<^bold>\<approx>)" by (simp add: symmetric_def setequ_equ)

(**We now encode connectives for (distributive and complemented) bounded lattices, mostly 
by reusing their counterpart meta-logical HOL connectives,*)
definition meet::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<and>" 54) 
  where "A \<^bold>\<and> B \<equiv> \<lambda>w. (A w) \<and> (B w)"
definition join::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<or>" 53) 
  where "A \<^bold>\<or> B \<equiv> \<lambda>w. (A w) \<or> (B w)"
definition top::"'w \<sigma>" ("\<^bold>\<top>")    
  where "\<^bold>\<top> \<equiv> \<lambda>w. True"
definition bottom::"'w \<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"

(**and introduce further operations to obtain a Boolean 'algebra of propositions'.*)
definition compl::"'w \<sigma> \<Rightarrow> 'w \<sigma>" ("\<^bold>\<midarrow>_"[57]58)
  where "\<^bold>\<midarrow>A  \<equiv> \<lambda>w. \<not>(A w)" (** (set-)complement*)
definition impl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<rightarrow>" 51)
  where "A \<^bold>\<rightarrow> B \<equiv> \<lambda>w. (A w) \<longrightarrow> (B w)" (** (set-)implication*)
definition diff::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<leftharpoonup>" 51) 
  where "A \<^bold>\<leftharpoonup> B \<equiv> \<lambda>w. (A w) \<and> \<not>(B w)" (** (set-)difference*)
definition dimpl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<leftrightarrow>" 51) 
  where "A \<^bold>\<leftrightarrow> B \<equiv> (A \<^bold>\<rightarrow> B) \<^bold>\<and> (B \<^bold>\<rightarrow> A)" (** double implication*)
definition sdiff::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<triangle>" 51) 
  where "A \<^bold>\<triangle> B \<equiv> (A \<^bold>\<leftharpoonup> B) \<^bold>\<or> (B \<^bold>\<leftharpoonup> A)" (** symmetric difference (aka. xor) *)

notation compl ("\<midarrow>") (** technical 'hack' so we can later refer to compl also as '\<midarrow>' *)
named_theorems conn (*to group together definitions for algebraic connectives*)
declare meet_def[conn] join_def[conn] top_def[conn] bottom_def[conn]
        impl_def[conn] dimpl_def[conn] diff_def[conn] sdiff_def[conn] compl_def[conn]

(**Verify characterization for some connectives.*)
lemma impl_diff_rel: "A \<^bold>\<leftharpoonup> B \<^bold>\<approx> \<^bold>\<midarrow>(A \<^bold>\<rightarrow> B)" by (simp add: conn setequ_char)
lemma dimpl_char: "(A \<^bold>\<leftrightarrow> B) = (\<lambda>w. (A w) = (B w))" by (metis dimpl_def impl_def meet_def)
lemma sdiff_char: "(A \<^bold>\<triangle> B) = (\<lambda>w. (A w) \<noteq> (B w))" by (metis diff_def join_def sdiff_def)

(**We can verify that (quite trivially) this algebra satisfies some properties of lattices.*)
lemma L1: "a = a \<^bold>\<or> a" by (simp add: conn)
lemma L2: "a = a \<^bold>\<and> a" by (simp add: conn)
lemma L3: "a \<^bold>\<preceq> a \<^bold>\<or> b" by (simp add: conn subset_def)
lemma L4: "a \<^bold>\<and> b \<^bold>\<preceq> a" by (simp add: conn subset_def)
lemma L5: "(a \<^bold>\<and> b) \<^bold>\<or> b = b" unfolding conn by blast 
lemma L6: "a \<^bold>\<and> (a \<^bold>\<or> b) = a" unfolding conn by blast
lemma L7: "a \<^bold>\<preceq> c \<Longrightarrow> b \<^bold>\<preceq> c \<Longrightarrow> a \<^bold>\<or> b \<^bold>\<preceq> c" by (simp add: conn subset_def) 
lemma L8: "c \<^bold>\<preceq> a \<Longrightarrow> c \<^bold>\<preceq> b \<Longrightarrow> c \<^bold>\<preceq> a \<^bold>\<and> b" by (simp add: conn subset_def)
lemma L9: "a \<^bold>\<preceq> b \<equiv> (a \<^bold>\<or> b) \<^bold>\<approx> b" by (smt (verit, best) conn setequ_char subset_def)
lemma L10: "b \<^bold>\<preceq> a \<equiv> (a \<^bold>\<and> b) \<^bold>\<approx> b" by (smt (z3) conn setequ_char subset_def)
lemma L11: "a \<^bold>\<preceq> b \<Longrightarrow> c \<^bold>\<preceq> d \<Longrightarrow> a \<^bold>\<or> c \<^bold>\<preceq> b \<^bold>\<or> d" by (simp add: conn subset_def)
lemma L12: "a \<^bold>\<preceq> b \<Longrightarrow> c \<^bold>\<preceq> d \<Longrightarrow> a \<^bold>\<and> c \<^bold>\<preceq> b \<^bold>\<and> d" by (simp add: conn subset_def)
lemma L13: "X \<^bold>\<and> \<^bold>\<top> = X" by (simp add: meet_def top_def)
lemma L14: "X \<^bold>\<or> \<^bold>\<bottom> = X" by (simp add: join_def bottom_def)

(**These properties below hold in particular for Boolean algebras.*)
lemma BA_distr1: "(a \<^bold>\<and> (b \<^bold>\<or> c)) = ((a \<^bold>\<and> b) \<^bold>\<or> (a \<^bold>\<and> c))" unfolding conn by blast
lemma BA_distr2: "(a \<^bold>\<or> (b \<^bold>\<and> c)) = ((a \<^bold>\<or> b) \<^bold>\<and> (a \<^bold>\<or> c))" unfolding conn by blast
lemma BA_cp: "a \<^bold>\<preceq> b \<equiv> \<^bold>\<midarrow>a \<^bold>\<succeq> \<^bold>\<midarrow>b" by (smt (verit, ccfv_threshold) conn subset_def)
lemma BA_deMorgan1: "\<^bold>\<midarrow>(X \<^bold>\<or> Y) = (\<^bold>\<midarrow>X \<^bold>\<and> \<^bold>\<midarrow>Y)" by (simp add: conn setequ_char)
lemma BA_deMorgan2: "\<^bold>\<midarrow>(X \<^bold>\<and> Y) = (\<^bold>\<midarrow>X \<^bold>\<or> \<^bold>\<midarrow>Y)" by (simp add: conn setequ_char)
lemma BA_dn: "\<^bold>\<midarrow>(\<^bold>\<midarrow> X) = X" by (simp add: compl_def)

(**This is another interesting and potentially useful property.*)
lemma img_inv_neg: "(X = \<^bold>\<midarrow>Y) \<longrightarrow> (\<lbrakk>\<phi> X\<rbrakk>\<inverse> = \<^bold>\<midarrow>\<lbrakk>\<phi> Y\<rbrakk>\<inverse>)" unfolding img_inv_def compl_def by simp

(**Some additional relevant definitions and properties*)

definition "meet_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<and> Y)"
definition "join_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<or> Y)"

definition "upwards_closed S \<equiv> \<forall>X Y. S X \<and> X \<^bold>\<preceq> Y \<longrightarrow> S Y"
definition "downwards_closed S \<equiv> \<forall>X Y. S X \<and> X \<^bold>\<succeq> Y \<longrightarrow> S Y"

lemma Disj_char: "Disj A B \<equiv> A \<^bold>\<and> B \<^bold>\<approx> \<^bold>\<bottom>" by (simp add: Disj_def bottom_def meet_def setequ_char)
lemma Cover_char: "Cover A B \<equiv> A \<^bold>\<or> B \<^bold>\<approx> \<^bold>\<top>" by (simp add: Cover_def join_def setequ_char top_def)

lemma DisjCover1: "Disj A B = Cover (\<^bold>\<midarrow>A) (\<^bold>\<midarrow>B)" by (simp add: Cover_def Disj_def compl_def)
lemma DisjCover2: "Cover A B = Disj (\<^bold>\<midarrow>A) (\<^bold>\<midarrow>B)" by (simp add: Cover_def Disj_def compl_def)
lemma subset_char: "A \<^bold>\<preceq> B \<equiv> Disj A (\<^bold>\<midarrow>B)" by (simp add: compl_def Disj_def subset_def)

definition singleton ("\<lbrace>_\<rbrace>") where "\<lbrace>x\<rbrace> \<equiv> \<lambda>y. y=x"
lemma singleton_diff: "\<forall>p q. p \<noteq> q \<longleftrightarrow> \<not>(\<lbrace>p\<rbrace> \<^bold>\<approx> \<lbrace>q\<rbrace>)" by (metis singleton_def setequ_equ)


subsection \<open>Transformations and relations on unary connectives\<close>

(**Unary connectives are particularly relevant for this work. 
  We define some (2nd-order) relations and transformations on them.*)

(**We define equality for unary connectives as follows.*)
definition op_equal::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> bool" (infix "\<^bold>\<equiv>" 60) 
  where "\<phi> \<^bold>\<equiv> \<psi> \<equiv> \<forall>X. \<phi> X \<^bold>\<approx> \<psi> X"

(**Moreover, we define the complement and the dual of a unary operator.*)
definition op_compl::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>c)") 
  where "\<phi>\<^sup>c \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi> X)"
definition op_dual::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>d)") 
  where "\<phi>\<^sup>d \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>X))"

named_theorems op_conn (*to group together definitions for operations on connectives*)
declare op_equal_def[op_conn] op_compl_def[op_conn] op_dual_def[op_conn] 

(**We now prove some lemmas (some of them might help provers in their hard work).*)
lemma op_equal_equ: "(\<phi> \<^bold>\<equiv> \<psi>) \<equiv> (\<phi> = \<psi>)" proof - (* why is this proof not totally automatic?*)
  have LtoR: "\<phi> \<^bold>\<equiv> \<psi> \<Longrightarrow> \<phi> = \<psi>" by (simp add: ext op_equal_def setequ_equ)
  have RtoL: "\<phi> = \<psi> \<Longrightarrow> \<phi> \<^bold>\<equiv> \<psi>" by (simp add: op_equal_def setequ_equ)
  from LtoR RtoL show "\<phi> \<^bold>\<equiv> \<psi> \<equiv> \<phi> = \<psi>" by linarith
qed 
lemma comp_symm: "\<phi>\<^sup>c \<^bold>\<equiv> \<psi> \<Longrightarrow> \<phi> \<^bold>\<equiv> \<psi>\<^sup>c" unfolding order conn op_conn by auto
lemma comp_invol: "\<phi>\<^sup>c\<^sup>c \<^bold>\<equiv> \<phi>" unfolding order conn op_conn by simp
lemma dual_symm: "(\<phi> \<^bold>\<equiv> \<psi>\<^sup>d) \<Longrightarrow> (\<psi> \<^bold>\<equiv> \<phi>\<^sup>d)" unfolding setequ_equ conn op_conn by simp
lemma dual_invol: "\<phi>\<^sup>d\<^sup>d \<^bold>\<equiv> \<phi>" unfolding order conn op_conn by simp
lemma dual_comp: "\<phi>\<^sup>d\<^sup>c \<^bold>\<equiv> \<phi>\<^sup>c\<^sup>d" unfolding order conn op_conn by simp

(**The notion of a fixed point is a fundamental one. We speak of propositions being fixed points of
operations. For a given operation we define in the usual way a fixed-point predicate for propositions.*)
definition fixpoint_pred::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> bool)" ("fp") 
  where "fp \<phi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<approx> X"
(**Indeed, we can 'operationalize' this fixed-point predicate by defining a fixed-point operator as follows:*)
definition fixpoint_op::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>f\<^sup>p)") 
  where "\<phi>\<^sup>f\<^sup>p  \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<leftrightarrow> X"

declare fixpoint_pred_def[op_conn] fixpoint_op_def[op_conn]

lemma fp_d: "(fp \<phi>\<^sup>d) X = (fp \<phi>)(\<^bold>\<midarrow>X)" unfolding order conn op_conn by auto
lemma fp_c: "(fp \<phi>\<^sup>c) X = (X \<^bold>\<approx> \<^bold>\<midarrow>(\<phi> X))" unfolding order conn op_conn by auto
lemma fp_dc:"(fp \<phi>\<^sup>d\<^sup>c) X = (X \<^bold>\<approx> \<phi>(\<^bold>\<midarrow>X))" unfolding order conn op_conn by auto

lemma ofp_c: "(\<phi>\<^sup>c)\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi>\<^sup>f\<^sup>p)\<^sup>c"  unfolding order conn op_conn by auto
lemma ofp_d: "(\<phi>\<^sup>d)\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi>\<^sup>f\<^sup>p)\<^sup>d\<^sup>c" unfolding order conn op_conn by auto
lemma ofp_dc:"(\<phi>\<^sup>d\<^sup>c)\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi>\<^sup>f\<^sup>p)\<^sup>d"  unfolding order conn op_conn by auto
lemma ofp_invol: "(\<phi>\<^sup>f\<^sup>p)\<^sup>f\<^sup>p \<^bold>\<equiv> \<phi>" unfolding order conn op_conn by auto

(**Fixed-point predicate and fixed-point operator are interrelated.*)
lemma fp_rel: "(fp \<phi>) X = (\<phi>\<^sup>f\<^sup>p X \<^bold>\<approx> \<^bold>\<top>)" unfolding order conn op_conn by auto
lemma fp_d_rel:  "(fp \<phi>\<^sup>d) X = (\<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>X) \<^bold>\<approx> \<^bold>\<top>)" unfolding order conn op_conn by auto
lemma fp_c_rel: "(fp \<phi>\<^sup>c) X = (\<phi>\<^sup>f\<^sup>p  X  \<^bold>\<approx> \<^bold>\<bottom>)" unfolding order conn op_conn by auto
lemma fp_dc_rel: "(fp \<phi>\<^sup>d\<^sup>c) X = (\<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>X) \<^bold>\<approx> \<^bold>\<bottom>)" unfolding order conn op_conn by auto

lemma fp_meet_join_closed_dual: "meet_closed (fp \<phi>) \<Longrightarrow> join_closed (fp \<phi>\<^sup>d)" 
  by (smt (verit) BA_deMorgan1 fp_d join_closed_def meet_closed_def setequ_equ)
lemma fp_join_meet_closed_dual: "join_closed (fp \<phi>) \<Longrightarrow> meet_closed (fp \<phi>\<^sup>d)"
  by (smt (verit, best) BA_deMorgan2 fp_d join_closed_def meet_closed_def setequ_equ)

end