theory base
  imports Main
begin

(*----------- Technicalities--------*)
declare[[smt_timeout=30]]
declare[[show_types]]
(* declare[[syntax_ambiguity_warning=false]] *)
sledgehammer_params[isar_proof=false]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3, atoms=a b c d] (*default Nitpick settings*)
(*we hide some Isabelle/HOL notation from the libraries (which we don't use) to avoid overloading*)
hide_const(open) List.list.Nil no_notation List.list.Nil ("[]")  (*We have no use for lists... *)
hide_const(open) Relation.converse no_notation Relation.converse ("(_\<inverse>)" [1000] 999) (*..nor for relations in this work*)
hide_const(open) Fun.comp no_notation Fun.comp (infixl "\<circ>" 55) (*we redefine function composition below*)
(*---------------------------------*)

section \<open>Basic definitions\<close>

(**We begin by introducing some useful(?) type aliases for frequently employed types.*)
type_synonym ('a,'b)\<rho> = \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close> (** for (curried) relations between 'a-type and 'b-type*)
type_synonym ('a,'b)\<phi> = \<open>'a \<Rightarrow> 'b\<close> (** for unary functions from 'a-type (domain) to 'b-type (codomain)*)
type_synonym ('a,'b)\<xi> = \<open>'a \<Rightarrow> 'a \<Rightarrow> 'b\<close> (** for (curried) binary functions from 'a-type to 'b-type*)
type_synonym ('a,'b)\<Phi> = \<open>('a \<Rightarrow> bool) \<Rightarrow> 'b\<close> (** for infinitary functions from 'a-type to 'b-type*)

(**In the sequel we employ the letters @{text "\<phi>"}, @{text "\<psi>"} and @{text "\<eta>"} to explicitly denote
unary functions/operations (e.g. type @{type "('a,'b)\<phi>"}); and the letters
@{text "\<xi>"} and @{text "\<delta>"} to denote binary functions/operations (e.g. type @{type "('a,'b)\<xi>"}).*)

(**Useful transformations on relations (on a same domain).*)
abbreviation symm_clsr::"('a,'a)\<rho> \<Rightarrow> ('a,'a)\<rho>" ("_\<^sup>C" [90]) 
  where \<open>\<rho>\<^sup>C a b \<equiv> \<rho> a b \<or> \<rho> b a\<close> (** Symmetric closure ('C' for Closure/Connected)*)
abbreviation symm_restr::"('a,'a)\<rho> \<Rightarrow> ('a,'a)\<rho>" ("_\<^sup>R" [90]) 
  where \<open>\<rho>\<^sup>R a b \<equiv> \<rho> a b \<and> \<rho> b a\<close> (** Symmetric restriction ('R' for clusteR/Reciprocal)*)
abbreviation strict_rel::"('a,'a)\<rho> \<Rightarrow> ('a,'a)\<rho>" ("_\<^sup>S" [90])
  where \<open>\<rho>\<^sup>S a b \<equiv> \<rho> a b \<and> \<not>\<rho> b a\<close> (** Strict variant*)

(**Useful well-known properties of relations.*)
definition \<open>reflexive \<rho> \<equiv> \<forall>a. \<rho> a a\<close>
definition \<open>transitive \<rho> \<equiv> \<forall>a b c. \<rho> a b \<and> \<rho> b c \<longrightarrow> \<rho> a c\<close>
definition \<open>wtransitive \<rho> \<equiv> \<forall>a b c. \<rho> a b \<and> \<rho> b c \<and> a \<noteq> c \<longrightarrow> \<rho> a c\<close> (*weak transitivity*)
definition \<open>symmetric \<rho> \<equiv> \<forall>a b. \<rho> a b \<longrightarrow> \<rho> b a\<close>
definition \<open>serial \<rho> \<equiv> \<forall>a. \<exists>b. \<rho> a b\<close>
definition \<open>antisymmetric \<rho> \<equiv> \<forall>a b. \<rho>\<^sup>R a b \<longrightarrow> a = b\<close>
definition \<open>connected \<rho> \<equiv> \<forall>a b. a \<noteq> b \<longrightarrow>  \<rho>\<^sup>C a b\<close>
definition \<open>sconnected \<rho> \<equiv> \<forall>a b. \<rho>\<^sup>C a b\<close> (*strongly connected*)
definition \<open>dense \<rho> \<equiv> \<forall>a b. \<rho>\<^sup>S a b \<longrightarrow> (\<exists>c. \<rho>\<^sup>S a c \<and> \<rho>\<^sup>S c b)\<close>


(**Function composition.*)
definition fun_comp :: "('b\<Rightarrow>'c)\<Rightarrow>('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'c" (infixl "\<circ>" 75) 
  where "\<phi> \<circ> \<psi> \<equiv> \<lambda>x. \<phi> (\<psi> x)"

(**Injectivity and surjectivity.*)
definition "injective \<phi> \<equiv> \<forall>x y. (\<phi> x) = (\<phi> y) \<longrightarrow> x = y"
definition "surjective \<phi> \<equiv> \<forall>y. \<exists>x. (\<phi> x) = y"
abbreviation "bijective \<phi> \<equiv> injective \<phi> \<and> surjective \<phi>"

(**Inverse is defined for bijective functions (only!).*)
definition inverse::\<open>('a,'b)\<phi> \<Rightarrow> ('b,'a)\<phi>\<close> ("_\<inverse>")
  where "\<phi>\<inverse> \<equiv> \<lambda>b. THE a. (\<phi> a = b)"

(**We verify some properties of inverse functions.*)
lemma inverse_char1: "bijective \<phi> \<Longrightarrow> (\<phi>\<inverse>\<circ>\<phi>) a = a" by (simp add: fun_comp_def injective_def inverse_def the_equality)
lemma inverse_char2: "bijective \<phi> \<Longrightarrow> (\<phi>\<circ>(\<phi>\<inverse>)) a = a" by (metis (no_types) fun_comp_def inverse_char1 surjective_def)
lemma "(\<phi>\<inverse>\<circ>\<phi>) A = A" nitpick oops (*counterexample if \<phi> is not assumed bijective*)
lemma inverse_invol: "bijective \<phi> \<Longrightarrow> (\<phi>\<inverse>)\<inverse> = \<phi>" by (metis (no_types) ext fun_comp_def injective_def inverse_char1 surjective_def)
lemma "(\<phi>\<inverse>)\<inverse> = \<phi>" nitpick oops (*counterexample if \<phi> is not assumed bijective*)

(**Predicate for indicating that a function @{text "\<phi>"} maps a domain into a codomain.*)
definition "mapping \<phi> Dom Cod \<equiv> \<forall>x. Dom x \<longrightarrow> Cod (\<phi> x)"

(**We can also define injectivity and surjectivity relative to a given domain/codomain.*)
definition "injectiveRel \<phi> Dom \<equiv> \<forall>x y. Dom x \<and> Dom y \<and> (\<phi> x) = (\<phi> y) \<longrightarrow> x = y"
definition "surjectiveRel \<phi> Dom Cod \<equiv> \<forall>y. Cod y \<longrightarrow> (\<exists>x. Dom x \<and> (\<phi> x) = y)"
abbreviation "bijectiveRel \<phi> Dom Cod \<equiv> injectiveRel \<phi> Dom \<and> surjectiveRel \<phi> Dom Cod"

(**Inverse (relativized to a given domain D) is defined only for \<phi> a bijective function (wrt. to D) 
 and an element b that is in the image of D under \<phi>.*)
definition inverseRel::\<open>('a,'b)\<phi> \<Rightarrow> ('a\<Rightarrow> bool) \<Rightarrow> ('b,'a)\<phi>\<close> ("_[_]\<inverse>")
  where "\<phi>[D]\<inverse> \<equiv> \<lambda>b. THE a. D a \<and> (\<phi> a = b)"

lemma map_comp: "mapping \<phi> A B \<and> mapping \<psi> B C \<longrightarrow> mapping (\<psi> \<circ> \<phi>) A C" 
  by (simp add: fun_comp_def mapping_def)

lemma inj_comp1: "mapping \<phi> A B \<and> mapping \<psi> B C \<and> injectiveRel \<phi> A \<and> injectiveRel \<psi> B 
                                          \<longrightarrow> injectiveRel (\<psi> \<circ> \<phi>) A"
  by (simp add: fun_comp_def injectiveRel_def mapping_def)
lemma inj_comp2: "mapping \<phi> A B \<and> mapping \<psi> B C \<and> injectiveRel \<psi> B \<and> injectiveRel (\<psi> \<circ> \<phi>) A
                                          \<longrightarrow> injectiveRel \<phi> A"
  by (simp add: fun_comp_def injectiveRel_def)

lemma surj_comp1: "mapping \<phi> A B \<and> mapping \<psi> B C \<and> surjectiveRel \<phi> A B \<and> surjectiveRel \<psi> B C
                                          \<longrightarrow> surjectiveRel (\<psi> \<circ> \<phi>) A C"
  by (smt (verit) fun_comp_def surjectiveRel_def)
lemma surj_comp2: "mapping \<phi> A B \<and> mapping \<psi> B C \<and> surjectiveRel \<phi> A B \<and>  surjectiveRel (\<psi> \<circ> \<phi>) A C
                                          \<longrightarrow> surjectiveRel \<psi> B C"
  by (smt (verit) fun_comp_def mapping_def surjectiveRel_def)

lemma bij_comp1: "mapping \<phi> A B \<and> mapping \<psi> B C \<and> bijectiveRel \<phi> A B \<and> bijectiveRel \<psi> B C
                                          \<longrightarrow> bijectiveRel (\<psi> \<circ> \<phi>) A C"
  by (meson inj_comp1 surj_comp1)
lemma bij_comp2: "mapping \<phi> A B \<and> mapping \<psi> B C \<and> bijectiveRel \<psi> B C \<and>  bijectiveRel (\<psi> \<circ> \<phi>) A C
                                          \<longrightarrow> bijectiveRel \<phi> A B"
  by (smt (verit) fun_comp_def injectiveRel_def mapping_def surjectiveRel_def)
lemma bij_comp3: "mapping \<phi> A B \<and> mapping \<psi> B C \<and> bijectiveRel \<phi> A B \<and>  bijectiveRel (\<psi> \<circ> \<phi>) A C
                                          \<longrightarrow> bijectiveRel \<psi> B C"
  by (smt (verit, ccfv_SIG) fun_comp_def injectiveRel_def mapping_def surjectiveRel_def)

lemma bij_inv: "(mapping \<phi> A B \<and> bijectiveRel \<phi> A B) \<longrightarrow> (mapping \<phi>[A]\<inverse> B A \<and> bijectiveRel \<phi>[A]\<inverse> B A)"
  unfolding inverseRel_def injectiveRel_def surjectiveRel_def mapping_def by (smt (z3) the_equality)

abbreviation "correspond1to1 A B \<equiv> \<exists>f. mapping f A B \<and> bijectiveRel f A B"

(**Swapping arguments for binary functions.*)
definition swap::\<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)\<close> ("_\<^sup>\<leftrightarrow>")
  where "\<xi>\<^sup>\<leftrightarrow> \<equiv> \<lambda>B A. \<xi> A B"

(**Projections map each a unary function into a 'projected' binary function.*)
definition proj1::\<open>('a,'b)\<phi> \<Rightarrow> ('a,'b)\<xi>\<close> ("\<^bold>\<pi>\<^sub>1")
  where "\<^bold>\<pi>\<^sub>1 \<phi> \<equiv> \<lambda>A B. \<phi> A"
definition proj2::\<open>('a,'b)\<phi> \<Rightarrow> ('a,'b)\<xi>\<close> ("\<^bold>\<pi>\<^sub>2")
  where "\<^bold>\<pi>\<^sub>2 \<phi> \<equiv> \<lambda>A B. \<phi> B"

(**Diagonalization maps a binary function into a unary function.*)
definition diag::\<open>('a,'b)\<xi> \<Rightarrow> ('a,'b)\<phi>\<close> ("\<langle>_\<rangle>")
  where "\<langle>\<xi>\<rangle> \<equiv> \<lambda>A. \<xi> A A"

(**Partial application maps a binary function @{text "\<xi>"} into a unary function (modulo an element E).
 It comes in two flavours (#1 or #2) depending on whether @{text "\<xi>"} is partially applied to the 
 element E at the second, resp. first position. This 'switched' notation has been chosen for convenience.
 To avoid confusion we suggest employing the provided notation only.*)
definition app1::\<open>('a,'b)\<xi> \<Rightarrow> 'a \<Rightarrow> ('a,'b)\<phi>\<close> ("\<lbrakk>_|'_ \<circ> _\<rbrakk>")
  where "\<lbrakk>\<xi>|_\<circ> E\<rbrakk> \<equiv> \<lambda>A. \<xi> A E" (*argument A comes in first place*)
definition app2::\<open>('a,'b)\<xi> \<Rightarrow> 'a \<Rightarrow> ('a,'b)\<phi>\<close> ("\<lbrakk>_|_ \<circ> '_\<rbrakk>")
  where "\<lbrakk>\<xi>|E \<circ>_\<rbrakk> \<equiv> \<lambda>A. \<xi> E A" (*argument A comes in second place*)

(**Projection and diagonalization are inverse in a sense.*)
lemma diag_proj1: \<open>\<langle>\<^bold>\<pi>\<^sub>1 \<phi>\<rangle> = \<phi>\<close> unfolding diag_def proj1_def by simp
lemma              \<open>\<^bold>\<pi>\<^sub>1\<langle>\<xi>\<rangle> = \<xi>\<close> nitpick oops (*counterexample - as expected*)
lemma diag_proj2: \<open>\<langle>\<^bold>\<pi>\<^sub>2 \<phi>\<rangle> = \<phi>\<close> unfolding diag_def proj2_def by simp
lemma              \<open>\<^bold>\<pi>\<^sub>2\<langle>\<xi>\<rangle> = \<xi>\<close> nitpick oops (*counterexample - as expected*)

(**Projection and partial-application are also inverse in a sense.*)
lemma app_proj1: \<open>\<lbrakk>\<^bold>\<pi>\<^sub>1 \<phi>|_ \<circ> X\<rbrakk> = \<phi>\<close> unfolding app1_def proj1_def by simp
lemma            \<open>\<lbrakk>\<^bold>\<pi>\<^sub>1 \<phi>|X \<circ> _\<rbrakk> = \<phi>\<close> nitpick oops (*counterexample - as expected*)
lemma            \<open>\<^bold>\<pi>\<^sub>1 \<lbrakk>\<xi>|_ \<circ> X\<rbrakk> = \<xi>\<close> nitpick oops (*counterexample - as expected*)
lemma app_proj2: \<open>\<lbrakk>\<^bold>\<pi>\<^sub>2 \<phi>|X \<circ> _\<rbrakk> = \<phi>\<close> unfolding app2_def proj2_def by simp
lemma            \<open>\<lbrakk>\<^bold>\<pi>\<^sub>2 \<phi>|_ \<circ> X\<rbrakk> = \<phi>\<close> nitpick oops (*counterexample - as expected*)
lemma            \<open>\<^bold>\<pi>\<^sub>2 \<lbrakk>\<xi>|X \<circ> _\<rbrakk> = \<xi>\<close> nitpick oops (*counterexample - as expected*)


(**Range, direct and inverse image of a unary function  @{text "\<phi>"}.*)
definition range::"('a,'b)\<phi> \<Rightarrow> ('b \<Rightarrow> bool)" ("\<lbrakk>_ -\<rbrakk>") 
  where "\<lbrakk>\<phi> -\<rbrakk> \<equiv> \<lambda>Y. \<exists>x. (\<phi> x) = Y"
definition img_dir::"('a,'b)\<phi> \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" ("\<lbrakk>_ _\<rbrakk>") 
  where "\<lbrakk>\<phi> S\<rbrakk> \<equiv> \<lambda>y. \<exists>x. (S x) \<and> (\<phi> x) = y"
definition img_inv::"('a,'b)\<phi> \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" ("\<lbrakk>_ _\<rbrakk>\<inverse>") 
  where "\<lbrakk>\<phi> S\<rbrakk>\<inverse> \<equiv> \<lambda>x. \<exists>y. (S y) \<and> (\<phi> x) = y"

lemma range_img_dir_char: "(\<lbrakk>\<phi> -\<rbrakk> X) = (\<exists>S. \<lbrakk>\<phi> S\<rbrakk> X)" unfolding range_def img_dir_def by blast

lemma img_dir_inv_equ: "injective \<phi> \<Longrightarrow> \<forall>S. \<lbrakk>\<phi> \<lbrakk>\<phi> S\<rbrakk>\<rbrakk>\<inverse> = S" unfolding injective_def img_dir_def img_inv_def by blast
lemma img_inv_dir_equ: "surjective \<phi> \<Longrightarrow> \<forall>S. \<lbrakk>\<phi> \<lbrakk>\<phi> S\<rbrakk>\<inverse>\<rbrakk> = S" (*TODO simplify proof*)
  unfolding surjective_def img_dir_def img_inv_def apply simp
  proof -
    assume surj: "\<forall>y. \<exists>x. \<phi> x = y"
    { fix S
      from surj have "\<forall>y. (\<exists>x. S (\<phi> x) \<and> \<phi> x = y) \<longleftrightarrow> S y" by metis
      hence  "(\<lambda>y. \<exists>x. S (\<phi> x) \<and> \<phi> x = y) = S" by simp
    }thus "\<forall>S. (\<lambda>y. \<exists>x. S (\<phi> x) \<and> \<phi> x = y) = S" by simp 
  qed

(**Dedekind definition of finite/infinite sets.*)
definition finite::"('a \<Rightarrow> bool) \<Rightarrow> bool" 
  where "finite A \<equiv> \<forall>f. mapping f A A \<and> injectiveRel f A \<longrightarrow> surjectiveRel f A A"
abbreviation infinite::"('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "infinite A \<equiv> \<not>finite A"

(**Prove some useful properties.*)
lemma finite_prop: "finite A \<Longrightarrow> \<forall>f. mapping f A A \<and> surjectiveRel f A A \<longrightarrow> injectiveRel f A" unfolding finite_def mapping_def injectiveRel_def surjectiveRel_def by metis
lemma infinite_prop: "infinite A \<Longrightarrow> \<exists>f. mapping f A A \<and> surjectiveRel f A A \<and> \<not>injectiveRel f A"
  oops (** as exercise *)

lemma finite1to1: "finite A \<and> correspond1to1 B A \<longrightarrow> finite B" proof -
  { assume finA: "finite A" and corrAB: "correspond1to1 B A"
    from corrAB obtain bij where mapBij: "mapping bij B A" and  bijBij: "bijectiveRel bij B A" by auto
    have "finite B" proof -
      { fix G
        { assume mapG: "mapping G B B"  and  injG: "injectiveRel G B"
          let ?h = "(bij \<circ> G) \<circ> bij[B]\<inverse>"
          have "mapping ?h A A \<and> injectiveRel ?h A" by (meson bijBij bij_inv injG inj_comp1 mapBij mapG map_comp)
          hence "surjectiveRel ?h A A" using finA finite_def by auto
          hence "surjectiveRel (bij \<circ> G) B A" by (meson bijBij bij_inv mapBij mapG map_comp surj_comp2)
          moreover from injG have "injectiveRel (bij \<circ> G) B" using bijBij inj_comp1 mapBij mapG by blast
          ultimately have "bijectiveRel (bij \<circ> G) B A" by simp
          hence "bijectiveRel G B B" using bijBij bij_comp2 mapBij mapG by blast
       }} thus ?thesis using finite_def by blast
    qed
  } thus ?thesis by simp
qed

end