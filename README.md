# BiSikkel: A Multimode Logical Framework in Agda (Artifact for POPL 2025)

This text provides instructions to use the Agda library called BiSikkel, as well as a description of its major components. Since this is the artifact for the POPL25 paper "BiSikkel: A Multimode Logical Framework in Agda", we indicate where all definitions and results in the paper can be found in the code.

## 1. Download, installation, and sanity-testing

This artifact is an Ubuntu 20.04 virtual machine containing an installation of Agda 2.7.0.1, the Agda standard library (version 2.1.1) and the BiSikkel library.

### 1.1 Downloading and running the VM

**Downloading**: Begin by downloading the latest version of the virtual machine.

**VirtualBox**: We used [VirtualBox](https://www.virtualbox.org/wiki/Downloads) v7.1.4 to prepare this artifact. The artifact has been prepared on a system running Ubuntu desktop 20.04.

**Importing the VM**: We follow the steps described in the VirtualBox [user manual](https://www.virtualbox.org/manual/UserManual.html#ovf-import-appliance). Go to `File > Import appliance`. Select the VM file `<...>/popl25-artifact30.ova`. An "Appliance settings" window is shown. The default values should be fine; in particular:

| Option                   | Value                                          |
| ------------------------ | ---------------------------------------------- |
| CPU (thread)             | 2                                              |
| RAM                      | 4096MB                                         |
| MAC address policy       | Include only NAT network adapter MAC addresses |
| Import hard drive as VDI | ticked box                                     |

Click on Finish. The VM should start importing (this could take a minute).

**Running the VM**: In VirtualBox, right click "POPL25 Artifact 30", and click `Start > Normal Start`.

### 1.2 Starting Agda, Emacs and BiSikkel

**First**: You can change your keyboard layout in `Settings (upper right corner) > Region & Language > Input Sources`. Your linux username is `vboxuser` and your password is `password`. You can open a terminal by hitting `Ctrl-Alt-T`.

**Agda & Emacs**: You can make sure that Agda is installed by issuing the command `agda --version`, which should report the Agda version 2.7.0.1. In order to make sure that Emacs and the Agda standard library are properly installed, open a terminal, go to `~/Desktop` and type `emacs test.agda`. This will open in Emacs a test Agda file that imports a module from the standard library. Load it by pressing `C-c C-l` (see Agda emacs [commands](https://agda.readthedocs.io/en/v2.6.3/tools/emacs-mode.html)). Everything works properly if the code has become colored and `*All Done*` appears at the bottom of the window.

**BiSikkel**: The BiSikkel library is located in `~/Desktop/bisikkel/`. In order to get the latest version, you can navigate there in a terminal and issue `git pull`. The simplest way to check that BiSikkel runs properly is to type-check it entirely. This can be done by opening a terminal, going to `~/Desktop/bisikkel/` and then running `make clean` followed by `make all` (see also Section 4.1 of this document). One will see that Agda starts type-checking all modules and it should not report any error or warning. This may take about 5 minutes.

**Remark about navigating files in Emacs**: In this document we will recommend to inspect many files of the BiSikkel library in Emacs and make Agda load (i.e. type-check) these files. This can be done as follows: open a terminal and go to `~/Desktop/bisikkel/`, then type `emacs &`. The command `C-x C-f` now lets you visit different files. When a file is opened, you can make Agda load it by typing `C-c C-l`.

### 1.3 (Optional) Manual installation of BiSikkel

It is also possible to manually install the BiSikkel library. This requires a working installation of Agda and of the Agda standard library. BiSikkel has been tested with the following combinations:

* Agda version 2.6.4.1 and Agda standard library version 2.0.

* Agda version 2.7.0.1 and Agda standard library version 2.1.1.

See [here](https://agda.readthedocs.io/en/v2.7.0.1/getting-started/installation.html) for installation instructions for Agda, and [here](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md) for installation instructions for the standard library.

The BiSikkel source files are available [here](https://github.com/JorisCeulemans/bisikkel). If you want to integrate BiSikkel in another Agda project, add the following line to your Agda libraries file (see [here](https://agda.readthedocs.io/en/v2.7.0.1/tools/package-system.html) for instructions where this is located): `$Path to local BiSikkel installation/bisikkel.agda-lib`. A project can now import BiSikkel modules by adding `bisikkel` as a dependency in its `.agda-lib` file. See also Section 6 of this document for instructions how to create your own instance of BiSikkel (i.e. specify a new mode theory, etc.).

## 2. List of claims (high-level)

In this section, we justify the claims made in the *contributions* section of the introduction (Section 1) of the paper. The correspondence between the rest of the paper and the Agda code will be discussed in the next section. For evaluation, one should verify that the mentioned Agda files can be loaded without error, warning or remaining goal, and that the mentioned functions (if any) have the expected type signature.

| Line | Claim                                                                                                                 | Artifact                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| ---- | --------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 111  | BiSikkel: an implemenation of MSTT and µLF as an Agda library                                                         | The implementation of MSTT can be found in `BiSikkel/MSTT/`, for µLF the implementation is located in `BiSikkel/LogicalFramework`.                                                                                                                                                                                                                                                                                                                                         |
| 113  | BiSikkel is parametrized by a mode theory.                                                                            | The BiSikkel definition of a mode theory is located in `BiSikkel/MSTT/Parameter/ModeTheory.agda`.                                                                                                                                                                                                                                                                                                                                                                          |
| 116  | We make Sikkel intrinsically typed and extend it with an equational theory.                                           | The intrinsically typed encoding of MSTT terms is defined as a data type `Tm` from line 92 to 132 in `BiSikkel/MSTT/Syntax/Terms.agda`. The equational theory is implemented in terms of fueled normalization (`BiSikkel/MSTT/Normalization.agda`).                                                                                                                                                                                                                        |
| 117  | We give the first implementation of Ceulemans et al.'s modal substitution algorithm and prove its substitution lemma. | The substitution algorithm is implemented in `BiSikkel/MSTT/Syntax/Substitution.agda`. One of the main results in that file is the function `_[_]tmʳˢ`, which is a general function for applying a renaming/substitution to an MSTT term. The proof of the substitution lemma can be found in `BiSikkel/MSTT/Soundness/Substitution.agda`.                                                                                                                                 |
| 120  | We implement a fueled normalization algorithm.                                                                        | The sound normalization algorithm can be found in `BiSikkel/MSTT/Normalization.agda` as the function `normalize`.                                                                                                                                                                                                                                                                                                                                                          |
| 123  | We prove BiSikkel sound by modeling µLF in a presheaf model of MTT.                                                   | The entire formalization of the presheaf model can be found in `BiSikkel/Model/`. The proof checker is implemented in `BiSikkel/LogicalFramework/Proof/Checker.agda` as the function `check-proof` and soundness proofs for all inference rules are located in `BiSikkel/LogicalFramework/Proof/Checker/Soundness.agda`.                                                                                                                                                   |
| 126  | We implement a proof extraction mechanism. In order to do so, we extend Sikkel's program extraction mechanism.        | Extraction for MSTT is reimplemented and extended (with respect to Sikkel) in `BiSikkel/MSTT/Extraction.agda`. We build further upon this in `BiSikkel/LogicalFramework/bProp/Extraction.agda` to extract propositions and in `BiSikkel/LogicalFramework/Proof/Extraction.agda` to extract proofs.                                                                                                                                                                         |
| 128  | We demonstrate the use of BiSikkel by proving properties of functions manipulating guarded streams.                   | The example proofs can be found in `Applications/GuardedRecursion/Examples/Proofs.agda`. The results discussed further on in the paper are `g-map-iterate` and `g-iterate-iterate'`. Apart from these examples, we also have a non-modal example (proving commutativity of natural number addition) in `Applications/NonModal/Examples.agda` and a form of representation independence using unary parametricity in `Applications/UnaryParametricity/BooleanExample.agda`. |

## 3. Paper-to-artifact correspondence (detailed)

In this section we discuss all definitions, results and code fragments that are included in the paper and we indicate where they can be found in the code base. Any differences between the paper and the library code will also be discussed. Like in the previous section, evaluation entails loading the Agda file without errors/warnings/remaining goals, and verifying the type signature of the mentioned functions.

### Section 2: A Brief Overview of Sikkel

#### Section 2.1: Syntactic Layer: Multimode Simple Type Theory (MSTT)

**Mode theory**: The mode theory as described on page 4 is implemented in `BiSikkel/MSTT/Parameter/ModeTheory.agda`. Note that a mode theory is a record of type `ModeTheory`, itself consisting of different other records. As already mentioned in footnote 5, the implementation of a mode theory is more complicated than described in the paper: when constructing a mode theory, one should only describe the non-trivial modes and modalities. The trivial mode `★` and the unit modality `𝟙` are automatically added. This has the advantage that some category laws hold strictly (i.e. up to Agda definitional equality). Furthermore, a mode theory in BiSikkel should also specify how modes, modalities, etc. are interpreted in the semantic layer as base categories, DRAs, etc. Finally, some soundness proofs of this interpretation should also be provided (e.g. the interpretation of a composite modality should be equivalent to the DRA composition of the modalities' interpretations).

**Types**: The definition of the data type `Ty` (Figure 3) can be found in `BiSikkel/MSTT/Syntax/Types.agda`. There we also see that there is a constructor `Ext` that allows a user to include new types in a BiSikkel instance (e.g. the type of guarded streams for the guarded recursion instance). This mechanism is further discussed in Section 6 of this readme file.

**Contexts**: The definition of the data type `Ctx` (Figure 3) is located in `BiSikkel/MSTT/Syntax/Contexts.agda`.

**Terms (intrinsically typed)**: The data type `Tm` is defined in `BiSikkel/MSTT/Syntax/Terms.agda`. One can verify that the constructors corresponding to the typing rules in Figure 4 do have a type signature that indeed encodes these inference rules (types and contexts of the conclusion and premises in the figure match those of the result and arguments of the constructor). Note that the modal elimination principle is called `mod-elim`, the let-syntax is only introduced on line 150. Note furthermore that the representation of variables is more complicated than in the paper (constructor `var'`): the De Bruijn index is represented as a value of type `Var x T Γ ◇`.  The constructors of this `Var` data type allow us to traverse `Γ` from the back to the point where we reach the required variable, and then the appropriate two-cell must be provided. The function `svar` is implemented on line 247.

#### Section 2.2: Semantic Layer: Presheaf Models

The formalization of presheaf models is located in `BiSikkel/Model/`. Note that this is a quite extensive development, and it is not really necessary to inspect it in order to use the library to write modal programs/proofs. Of course, one should understand more details when implementing a new instance of BiSikkel.

The interpretation of modes as base categories (see `BiSikkel/Model/BaseCategory.agda`), modalities as dependent adjunctions (DRAs, see `BiSikkel/Model/DRA/Basics.agda`) and two-cells as natural transformations (also called `TwoCell` in the formalization, see `BiSikkel/Model/DRA/TwoCell.agda`) should be specified in a mode theory (`BiSikkel/MSTT/Parameter/ModeTheory.agda`).

The interpretation functions for types and contexts can be found in `BiSikkel/MSTT/Interpretation/TypeContext.agda` as `⟦_⟧ty` and `⟦_⟧ctx` respectively. Note that types are interpreted as a semantic `ClosedTy`, which is the way to specify in our dependently typed formalization of presheaf models (see footnote 8) that a semantic type is actually not dependent (since MSTT is *simply* typed).

The interpretation function for terms is `⟦_⟧tm` in `BiSikkel/MSTT/Interpretation.agda`.

#### Section 2.3: Extraction to the Meta-level

The original extraction mechanism from Sikkel is not included in BiSikkel because we completely reimplemented it. For MSTT, the mechanism can be found in `BiSikkel/MSTT/Extraction.agda`.

### Section 3: Why a Dedicated Logical Framework?

**Guarded recursion mode theory (Figure 5a)**: The mode theory for guarded recursive type theory is implemented in `Applications/GuardedRecursion/BiSikkel/ModeTheory.agda`. Compared to Figure 5a, the implementation does not only contain the 3 modalities in the figure but also all of their compositions (taking the equalities in the figure into account). Similarly the data type of two-cells (`TwoCell`) also contains the horizontal and vertical compositions arising from the trivial cell and the cells shown in the figure. The semantics of the modalities for guarded recursion are located in `Applications/GuardedRecursion/Model/Modalities/`.

**Guarded streams primitives (Figure 5b)**: The inclusion of the type constructor `GStream` in the syntax layer of the BiSikkel instance is done in `Applications/GuardedRecursion/BiSikkel/TypeExtension.agda`. Similarly, the new term constructors for guarded recursion are specified in `Applications/GuardedRecursion/BiSikkel/TermExtension.agda`. The function `tm-code-ty` specifies the result type for every new term constructor, and the function `tm-code-arginfos` specifies the type and context modifications for all arguments to the term constructors. The semantics of guarded streams can be found in `Applications/GuardedRecursion/Model/Streams/Guarded.agda`.

**Implementation of guarded stream functions (Figure 6)**: The functions from Figure 6 are implemented in `Applications/GuardedRecursion/Examples/Streams.agda`. The rest of that file contains some more examples of guarded streams, and also of standard streams and extraction as described on lines 416-421 of the paper.

### Section 4: µLF, a Proof System for MSTT

#### Section 4.1: Propositions & Proof Contexts

**Propositions**: The data type `bProp` from Figure 7a is defined in `BiSikkel/LogicalFramework/bProp/Syntax.agda`. It does include an extra constructor `ext` that can be used to extend BiSikkel with custom proposition connectives for specific applications. The definition of "non-modal" implication `⊃` can be found on line 148. It uses a key renaming to introduce the (trivial) lock required in the domain proposition for the constructor `⟨_∣_⟩⊃_`.

**Proof contexts**: The data type `ProofCtx` and function `to-ctx` from Figure 7b are defined in `BiSikkel/LogicalFramework/Proof/Context.agda`.

#### Section 4.2: Axioms & Inference Rules

**Substitution**: As in the paper, we defer details about substitution to Section 5.4. The definition of the type `Sub` together with the functions `_[_]tm` and `_[_]bprop` can be found in `BiSikkel/MSTT/Syntax/Substitution.agda`. Also the definitions of `_/_` and `_//_` are located on lines 445 and 448 respectively in that file.

**β-equivalence for terms**: As discussed in the paper, this is implemented via a fueled normalization function in BiSikkel. There is no mechanized treatment of the axiomatic system. However, one can see the rule TmEq-Fun implemented on lines 83-85 in `BiSikkel/MSTT/Normalization.agda` where the term *s* from the inference rule has been replaced by `b` and *t* by `nt`. Similarly, the rule TmEq-Mod is implemented on lines 51-52 of the same file. The function `fuselocks-tm` is used to make the term we are substituting type-check in the right context, as discussed in the paper.

**The proof system**: The inference rules of µLF are not explicitly encoded in BiSikkel. Instead, one can take a look at the definition of the data type `Proof` in `BiSikkel/LogicalFramework/Proof/Definition.agda` (the premises and conclusion for every constructor are also given there as comments) and the proof checking function `check-proof` in `BiSikkel/LogicalFramework/Proof/Checker.agda`. As an example, let us look at the case for `sym` in `check-proof` (lines 65-68): first we make sure that the proposition `φ` we want to assign to the proof `sym p` is an equality and bind the two sides to `t1` and `t2`. Then we check that `p` is a valid proof of the proposition `t2 ≡ᵇ t1` in the same context (we do not worry about goals or evidence `⟦p⟧` at this moment). If this succeeds, we return successfully, and again we do not worry about goals or evidence yet. As we can see, this is indeed a way to check the rule Prf-≡ᵇ-Sym in the paper. In this way, every rule from Figure 9 has a corresponding constructor in the `Proof` data type and a case in the proof checker. We will now discuss the exceptions:

* The rule Prf-Beta is not actually implemented in BiSikkel. Instead, there is a proof construct `with-normalization p` which allows to prove an equality of terms, if `p` proves the equality of their normalizations. Taking `p` to be `refl`, one can immediately show equality of any two β-equivalent terms. Combining this with the proof constructor `subst`, we can transform a proof of a proposition φ to a proof of a proposition ψ which only differs from φ in that some terms may have been replaced by β-equivalent ones. In this way the rule Prf-Beta is admissible. Furthermore, if really needed, it would not be too hard to extend normalization to propositions and actually implement Prf-Beta.

* There is a proof constructor `by-unfold-global-def`, which is not covered in Figure 9. This has to do with a term constructor `global-def` that is used for extraction (it allows a term defined in the empty context to be used in any context). From a theoretical point of view, `global-def` just applies a terminal substitution (with the empty context as codomain) to a term and is otherwise completely transparent, which is what the proof constructor above proves.

* The rule Prf-Mod-Elim is slightly more complicated. As it is in Figure 9, it would not type-check because φ would need to live in both `to-ctx Ξ ,lock⟨ ρ ⟩ ,lock⟨ μ ⟩` and `to-ctx Ξ ,lock⟨ ρ ⓜ μ ⟩`, which are not exactly the same contexts. This difference can however be bridged using a renaming, which is what `fuse-locks-bprop` does in the BiSikkel version of Prf-Mod-Elim (proof constructor `mod-elim`).

* There are proof constructors `cong` and `fun-cong` which express congruence of the application term constructor `∙` in its second and its first argument respectively (with respect to bProp equality). These constructors do not explicitly correspond to a proof rule in Figure 9, but they are admissible via the rule Prf-≡ᵇ-Subst.

* There are proof constructors `hole` for inserting a hole in a proof and `ext` for extending the BiSikkel proof system with new inference rules. These do not correspond to a rule in Figure 9.

#### Section 4.3: Continuing the g-iterate Example

**New β-equivalence and proof rules for guarded recursion (Figure 10)**: The implementation of rule TmEq-GStream-Head in the normalizer can be found on line 52 of `Applications/GuardedRecursion/BiSikkel/Normalization.agda`. Similarly TmEq-GStream-Tail is located on line 62 of that file. The proof checker implementations for the rules Prf-TmLöb-Beta and Prf-Löb are realized via the function `pf-code-check` in `Applications/GuardedRecursion/BiSikkel/ProofExtension.agda`.

**Lemma about g-map and g-iterate**: The proposition we want to prove is called `g-map-iterate` and can be found on line 122 of `Applications/GuardedRecursion/Examples/Proofs.agda`. The actual proof is immediately below the proposition and is called `g-map-iterate-proof`. Note that, just like in the paper (equation (6)), the proof starts with two invocations of the introduction rule for ∀, and then the Löb induction rule for proofs, after which an equality chain follows. The equality chain is similar to steps (7-11) in the paper; in the Agda code the proofs for the different steps are included between the angular brackets immediately following the `≡ᵇ` symbols. As mentioned in the paper, step (7) is not included. Step (8) indeed makes use of Prf-TmLöb-Beta, encoded in the BiSikkel instance as `tmlöb-β` (the use of `with-normalization` has to do with the fact that terms need to be normalized, e.g. to have step (7) be automatically verified). The proof of the lemma mentioned in step (9) is called `g-map-cons-proof` and we apply the elimination principle for ∀ three times to this result. The admissible rule Gcons-Cong used in step (10) is proved in the same file under the name `g-cons-cong`. Note that in step (10) we also use the induction hypothesis named `"ih"` on line 156. Finally, step (11) uses again β-equivalence and `tmlöb-β` as mentioned in the paper (line 159). Note that the syntax `≡ᵇ⟨ with-normalization tmlöb-β ⟨` with the inverted angular bracket in the end, automatically applies `sym` (so it actually provides a proof of the reversed equality). Finally, the function `IsOk` is defined in `BiSikkel/LogicalFramework/Proof/CheckingMonad.agda` and is defined as Agda's unit type `⊤` upon success and the empty type `⊥` upon failure of a computation in the proof checking monad. As a result, the fact that we can provide a value of `IsOk (check-proof ◇ (g-map-iterate-proof Nat') (g-map-iterate Nat'))` on line 162-163 of `Applications/GuardedRecursion/Examples/Proofs.agda` means that the proof checker accepts our proof of `g-map-iterate`.

**Final result about g-iterate and g-iterate'**: The proposition is called `g-iterate-iterate'` and is defined on line 169 of `Applications/GuardedRecursion/Examples/Proofs.agda`. It is immediately followed by its proof `g-iterate-iterate'-proof` on line 176. As described in the paper, we subsequently use `∀-intro`, `pflöb` and again `∀-intro`, after which the equality chain (steps (12-15)) follows. The equality chain is similar to the lemma. One can indeed verify that the steps in the paper are included in the BiSikkel proof. For the last step, we use a lemma `g-iterate'-cons`, whereas the paper claims to use only unfolding of definitions, β-reduction and the use of Prf-TmLöb-Beta. The lemma indeed only makes use of these principles, but we need an intermediate step since Prf-TmLöb-Beta cannot immediately be applied to the normalized versions of both sides of the equation.

**Relaing iterate and iterate'**: As stated on lines 841-845 in the paper, we can prove a similar result relating `iterate` and `iterate'` for standard streams in BiSikkel. This is proven in `iterate-iterate'-proof` in `Applications/GuardedRecursion/Examples/Proofs.agda`. Contrary to the claim in the paper, extraction does work but as explained in the code, it takes too much time to compare the inferred type of the extracted result to the expected Agda type. This will be made clear in the revised version of the paper.

#### Section 4.4: Another Example: Unary Parametricity

Contrary to the claim in the paper on line 853, this example is now finished.

The definition of the mode theory is located in `Applications/UnaryParametricity/BiSikkel/ModeTheory.agda`, the extension with `EncBool`in `Applications/UnaryParametricity/BiSikkel/TypeExtension.agda`. The semantics behind the modalities and type/term formers (including the predicate of Booleanness on natural numbers) can be found in `Applications/UnaryParametricity/Model.agda`. The extension of BiSikkel with a new bProp constructor is located in `Applications/UnaryParametricity/BiSikkel/bPropExtension.agda` and the new proof rules in `Applications/UnaryParametricity/BiSikkel/ProofExtension.agda`. Note that the assertion `Γ ⊢ Pred C (mod⟨ forget ⟩ c)` is proved via a proof constructor `param` and what the paper calls Reynolds's definition of the logical relation for the function type is proved via `extent-from` (we only include one side of the equivalence).

We can then construct the proof claimed in the paper in the file `Applications/UnaryParametricity/BooleanExample.agda` and we refer to the comments in the Agda code there. Note that similar to guarded recursion, proof extraction works but comparing the resulting type to the expected Agda type is very slow. We will mention this in the revised version of the paper.

### Section 5: Implementation of µLF in Agda

#### Section 5.1: Agda Representation of Proofs

The definition of the data type `Proof` (i.e. the extrinsically typed representation) can be found in `BiSikkel/LogicalFramework/Proof/Definition.agda`.

#### Section 5.2: The Proof Checker

**Interpretation of propositions and proof contexts**: The function `⟦_⟧bprop` interpreting propositions in the presheaf model, is located in `BiSikkel/LogicalFramework/bProp/Interpretation.agda`. For the definitions of `⟦_⟧pctx` interpreting proof contexts and `to-ctx-subst` providing a semantic substitution, we refer to lines 135-146 of `BiSikkel/LogicalFramework/Proof/Context.agda`.

**Proof checking monad**: The proof checking monad and associated operations are defined in `BiSikkel/LogicalFramework/Proof/CheckingMonad.agda`.

**Goals (Figure 11)**: Goals and the result type of the proof checker are defined in `BiSikkel/LogicalFramework/Proof/Checker/ResultType.agda`.

**The proof checker**: The actual implementation of the proof checker can be found in `BiSikkel/LogicalFramework/Proof/Checker.agda`. Soundness of all the cases for the proof checker is proved in `BiSikkel/LogicalFramework/Proof/Checker/Soundness.agda`.

#### Section 5.3: Proof Extraction

Extraction of MSTT contexts, types and terms is defined in `BiSikkel/MSTT/Extraction.agda`. Instances of extractability for many of the MSTT standard type and term constructors can also be found there. Extraction of propositions (as well as many instances) is defined in `BiSikkel/LogicalFramework/bProp/Extraction.agda`. Finally, proof extraction is implemented in `BiSikkel/LogicalFramework/Proof/Extraction.agda`.

The proof of commutativity of natural number addition is located in `Applications/NonModal/Examples.agda`. The illustration of the extraction mechanism for this example can be found on line 166 of that file.

#### Section 5.4: Substitution and (Fueled) Normalization for MSTT

**Substitution**: The substitution algorithm is implemented in `BiSikkel/MSTT/Syntax/Substitution.agda`. In order to capture the behaviour of pushing a substitution/renaming through term constructors until a variable is reached, we also introduce the concept of term traversals there. The soundness of the substitution algorithm with respect to the presheaf model of MSTT is proven in `BiSikkel/MSTT/Soundness/Substitution.agda`. This proof largely follows the structure of the implementation of the substitution algorithm (traversals, atomic and regular rensubs, etc.)

**Fueled Normalization**: The result type of normalization as shown on page 23 is defined in `BiSikkel/MSTT/Normalization/ResultType.agda`. The actual normalization function is then implemented in `BiSikkel/MSTT/Normalization.agda`.

## 4. Further evaluation instructions

### 4.1 Checking Everything

Apart from inspecting all aspects described in the previous sections, it is important to verify that the entire BiSikkel library can be type-checked by Agda without producing errors or warnings (a warning would be issued e.g. when there are goals that still need to be solved). For this purpose, one can go to the root of the BiSikkel project and make sure that the file `Everything.agda` is not present. Then running `make all` will generate an Agda file `Everything.agda` that imports all Agda files contained in BiSikkel and subsequently let Agda type-check it via `agda -i . Everything.agda` (this last command is executed by make, we show it here to illustrate that warnings are not suppressed).

### 4.2 Postulates

By running `rgrep postulate .` in the BiSikkel project root, one can verify that there are only 2 files where an axiom is postulated:

* In `BiSikkel/Preliminaries.agda` we postulate function extensionality for regular and for implicit Agda functions. Although we avoid using this axiom, function extensionality is used e.g. in the presheaf formalization of function types.

* In `Applications/GuardedRecursion/Preliminaries.agda` we use stream extensionality. This is only not used in the BiSikkel library itself, but only in the guarded recursion instance. Moreover, it is only necessary to provide an extractability instance for standard BiSikkel streams in `Applications/GuardedRecursion/BiSikkel/MSTT.agda` (line 67, which uses  `growvec-stream-iso` and that function is the only one to use `streamext` as can be verified by running `rgrep streamext .`).

Both function extensionality and stream extensionality are uncontroversial axioms which are regularly added to standard Martin-Löf type theory.

### 4.3 Command-line Options and Pragmas

By running `rgrep OPTIONS .` in the BiSikkel project root, one can see that the only command-line option used is the `--guardedness` flag which is needed to provide a coinductive defintion of Agda streams. The use of this flag is also restricted to the guarded recursion instance.

The only pragma that is used is an innocent display pragma in `BiSikkel/MSTT/Syntax/Types.agda`. This can be verified by running `rgrep "{-#" .` in the BiSikkel project root.

## 5. Structure of the BiSikkel library

* `BiSikkel/` contains the reusable part of the BiSikkel library and is intended to be instantiated with different mode theories.
  
  * `BiSikkel/Model/` contains the semantic layer (i.e. Presheaf Models) of Figure 2 in the paper. It is a reworked version of the formalization of presheaf models of type theory from the [Sikkel library](https://github.com/JorisCeulemans/sikkel/releases/tag/v1.0).
  
  * `BiSikkel/MSTT/` contains the intrinsically typed formalization of MSTT: definition of syntax, interpretation in a presheaf model, substitution algorithm, fueled normalization function, ...
    
    * `BiSikkel/MSTT/Parameter/` contains all parameters relevant to MSTT: mode theory, type extension, term extension.
  
  * `BiSikkel/Parameter/` contains all parameters that are not relevant for MSTT: proposition extension and proof extension.
  
  * `BiSikkel/LogicalFramework/` contains the implementation of the µLF framework in Agda.
    
    * `BiSikkel/LogicalFramework/bProp/` contatains everything related to propositions: definition of their syntax, substitution algorithm, interpretation in presheaf model, ...
    
    * `BiSikkel/LogicalFramework/Proof/` contains everything related to proofs: definition of proofs, proof contexts, the proof checking monad, the proof checker, (sound) testing procedure for α-equivalence of MSTT programs, soundness proofs for the µLF inference rules, ...
  
  * Extraction (the bottom layer in Figure 2) is spread across the library: extraction for MSTT contexts, types and terms is defined in `BiSikkel/MSTT/Extraction.agda`. Extraction for propositions is defined in `BiSikkel/LogicalFramework/bProp/Extraction.agda` and for proof contexts and proofs in `BiSikkel/LogicalFramework/Proof/Extraction.agda`.

* `Applications/` contains instances and usage examples of BiSikkel (many of which are described in the paper).
  
  * `Applications/GuardedRecursion/` is the most mature instance, providing a framework to work with guarded recursive type theory. It also includes example programs manipulating guarded streams and proofs of some of their properties.
  
  * `Applications/NonModal/` is a very simple instance with one mode and only the trivial modality (and no extra type, term, proposition or proof constructors). As an example we show commutativity of natural number addition using BiSikkel.
  
  * `Applications/UnaryParametricity/` contains an instance for unary parametricity as described in Section 4.4 of the paper. This also contains the toy example about Booleans represented as natural numbers 0 and 1.

## 6. Creating a BiSikkel instance

In order to construct a new instance of BiSikkel for a certain modal application, one has to provide several pieces of information, which we list below. We also encourage to take a look at the implementation of the existing instances in the `Applications` folder.

Basically, a complete instance of BiSikkel can be provided by constructing a record of type `BiSikkelParameter` as defined in `BiSikkel/Parameter.agda`. This amounts to specifying the following structure:

* An `MSTT-parameter` as defined in `BiSikkel/MSTT/Parameter.agda`:
  
  * A `ModeTheory` as defined in `BiSikkel/MSTT/Parameter/ModeTheory.agda`.
  
  * A `TyExt` record as defined in `BiSikkel/MSTT/Parameter/TypeExtension.agda`. This allows a user to specify a universe (i.e. an Agda type) of codes, each of which will give rise to a new type constructor. For every code some extra structure needs to be given, e.g. one must specify how the new type constructors should be interpreted in a presheaf model and prove that these interpretations satisfy a naturality condition.
  
  * A `TmExt` record as defined in `BiSikkel/MSTT/Parameter/TermExtension.agda`. This allows to specify a universe of codes for new term constructors (with extra information such as their type and the context modifications for their subterms).
  
  * A `TmExtSem` record as defined in `BiSikkel/MSTT/Parameter/TermExtensionSemantics.agda`, specifying how the new term constructors should be interpreted in a presheaf model.
  
  * A `TmExtNormalization` record as defined in `BiSikkel/MSTT/Parameter/TermExtensionNormalization.agda` specifying what the normalization function should do with the newly added term constructors.

* A `bPropExt` record as defined in `BiSikkel/Parameter/bPropExtension.agda`. This will again specify a universe of codes, each of which gives rise to a new bProp constructor. For every code, one has to specify some extra structure, e.g. how contexts should be modified in subpropositions.

* A `bPropExtSem` record as defined in `BiSikkel/Parameter/bPropExtensionSemantics.agda` specifying how the new bProp constructors should be interpreted in a presheaf model and proving some properties of these interpretations (e.g. naturality).

* A `ProofExt` record as defined in `BiSikkel/Parameter/ProofExtension.agda`. This once again specifies a universe of codes for new proof constructors. One also has to specify the new cases for the proof checker for every new proof constructor.
