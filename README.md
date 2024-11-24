# BiSikkel: A Multimode Logical Framework in Agda

BiSikkel is an Agda library that allows a user to write programs and proofs in multimode type theory. It consists of a program layer (MSTT or multimode simple type theory, a complete reworking of the MSTT implementation of [Sikkel](https://github.com/JorisCeulemans/sikkel/releases/tag/v1.0)) and a logical framework in which program properties can be proved. Both layers are parametrised by a mode theory specifying modes, modalities and two-cells. Moreover, the program layer can be extended with new type and term formers and the logical framework with new proposition formers and proof rules, depending on the application. We illustrate BiSikkel's usage by writing functions that manipulate streams and proving properties about them in guarded type theory and by proving a result using unary parametricity.

More details can be found in the POPL25 paper [BiSikkel: A Multimode Logical Framework in Agda](https://doi.org/10.1145/3704844).

## Installation

BiSikkel depends on Agda and its standard library. Our library has been tested with the following combinations:

* Agda version 2.6.4.1 and Agda standard library version 2.0,

* Agda version 2.7.0.1 and Agda standard library version 2.1.1.

See [here](https://agda.readthedocs.io/en/v2.7.0.1/getting-started/installation.html) for installation instructions for Agda, and [here](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md) for installation instructions for the standard library.

In order to get BiSikkel on your system, perform

```
git clone https://github.com/JorisCeulemans/bisikkel.git
```

You can type-check the entire library by executing `make all` in the `bisikkel` directory. If you want to use BiSikkel in your Agda development, add the following line to your Agda libraries file (see [here](https://agda.readthedocs.io/en/v2.7.0.1/tools/package-system.html) for instructions where this is located): `$Path to local BiSikkel installation/bisikkel.agda-lib`. A project can now import BiSikkel modules by adding `bisikkel` as a dependency in its `.agda-lib` file. See also further in this readme file for instructions on how to create your own instance of BiSikkel (i.e. specify a new mode theory, etc.).

## Structure of the BiSikkel library

* `BiSikkel/` contains the reusable part of the BiSikkel library and is intended to be instantiated with different mode theories.
  
  * `BiSikkel/Model/` contains the semantic layer (i.e. presheaf models) of Figure 1b in the POPL paper. It is a reworked version of the formalisation of presheaf models of type theory from the [Sikkel library](https://github.com/JorisCeulemans/sikkel/releases/tag/v1.0).
  
  * `BiSikkel/MSTT/` contains an intrinsically typed formalisation of MSTT: definition of syntax, interpretation in a presheaf model, substitution algorithm, fueled normalisation function, ...
    
    * `BiSikkel/MSTT/Parameter/` contains all parameters relevant to MSTT: mode theory, type extension, term extension.
  
  * `BiSikkel/Parameter/` contains all parameters that are not relevant for MSTT: proposition extension and proof extension.
  
  * `BiSikkel/LogicalFramework/` contains an implementation of the µLF framework in Agda.
    
    * `BiSikkel/LogicalFramework/bProp/` contains everything related to propositions: definition of their syntax, substitution algorithm, interpretation in presheaf model, ...
    
    * `BiSikkel/LogicalFramework/Proof/` contains everything related to proofs: definition of proofs, proof contexts, the proof checking monad, the proof checker, (sound) testing procedure for α-equivalence of MSTT programs, soundness proofs for the µLF inference rules, ...
  
  * Extraction (the bottom layer in Figure 1b of the POPL paper) is spread across the library: extraction for MSTT contexts, types and terms is defined in `BiSikkel/MSTT/Extraction.agda`. Extraction for propositions is defined in `BiSikkel/LogicalFramework/bProp/Extraction.agda` and for proof contexts and proofs in `BiSikkel/LogicalFramework/Proof/Extraction.agda`.

* `Applications/` contains instances and usage examples of BiSikkel (many of which are described in the POPL paper).
  
  * `Applications/GuardedRecursion/` is the most mature instance, providing a framework to work with guarded recursive type theory. It also includes example programs manipulating guarded streams and proofs of some of their properties.
  
  * `Applications/NonModal/` is a very simple instance with one mode and only the trivial modality (and no extra type, term, proposition or proof constructors). As an example we show commutativity of natural number addition using BiSikkel.
  
  * `Applications/UnaryParametricity/` contains an instance for unary parametricity as described in Section 4.4 of the POPL paper. This also contains the toy example about Booleans represented as natural numbers 0 and 1.

## Creating a BiSikkel instance

In order to construct a new instance of BiSikkel for a certain modal application, one has to provide several pieces of information, which we list below. We also encourage to take a look at the implementation of the existing instances in the `Applications` folder.

Basically, a complete instance of BiSikkel can be provided by constructing a record of type `BiSikkelParameter` as defined in `BiSikkel/Parameter.agda`. This amounts to specifying the following structure:

* An `MSTT-parameter` as defined in `BiSikkel/MSTT/Parameter.agda`:
  
  * A `ModeTheory` as defined in `BiSikkel/MSTT/Parameter/ModeTheory.agda`.
  
  * A `TyExt` record as defined in `BiSikkel/MSTT/Parameter/TypeExtension.agda`. This allows a user to specify a universe (i.e. an Agda type) of codes, each of which will give rise to a new type constructor. For every code some extra structure needs to be given, e.g. one must specify how the new type constructors should be interpreted in a presheaf model and prove that these interpretations satisfy a naturality condition.
  
  * A `TmExt` record as defined in `BiSikkel/MSTT/Parameter/TermExtension.agda`. This allows a user to specify a universe of codes for new term constructors (with extra information such as their type and the context modifications for their subterms).
  
  * A `TmExtSem` record as defined in `BiSikkel/MSTT/Parameter/TermExtensionSemantics.agda`, specifying how the new term constructors should be interpreted in a presheaf model.
  
  * A `TmExtNormalization` record as defined in `BiSikkel/MSTT/Parameter/TermExtensionNormalization.agda` specifying what the normalisation function should do with the newly added term constructors.

* A `bPropExt` record as defined in `BiSikkel/Parameter/bPropExtension.agda`. This will again specify a universe of codes, each of which gives rise to a new bProp constructor. For every code, one has to specify some extra structure, e.g. how contexts should be modified in subpropositions.

* A `bPropExtSem` record as defined in `BiSikkel/Parameter/bPropExtensionSemantics.agda` specifying how the new bProp constructors should be interpreted in a presheaf model and proving some properties of these interpretations (e.g. naturality).

* A `ProofExt` record as defined in `BiSikkel/Parameter/ProofExtension.agda`. This once again specifies a universe of codes for new proof constructors. One also has to specify the new cases for the proof checker for every new proof constructor.
