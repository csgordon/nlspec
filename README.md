# Natural Language Specifications for Coq

This repository holds the prototype implementation accompanying the ITP 2019 submission "Natural Language Specifications (Short Paper)"

The files within are:

- ```CCG.v```: Formalization of the grammar types and their interpretation, with some notation.
- ```_CoqProject```: Coq project file for compiling everything
- ```Dictionary.v```: The lexicon file, containing the grammatical role and definition for a few words
  + Currently "non-negative" from the submission is truncated to "nonneg" because our string tokenization approach has fixed recognizers for words of length n, for n in 1..8. We have opted to abbreviate for now while seeking a better tokenization strategy, rather than generating the boilerplate out to [20 or more letters](https://en.wikipedia.org/wiki/Longest_word_in_English)
- ```README.md```: This file
- ```Specs.v```: The file defining the ```spec``` construct, coupling tokenization to grammatical parsing and denotation
- ```StringSplit.v```: String splitting on whitespace
- ```Testing.v```: A range of examples
  + This file including both examples *using* NL specifications (```Goal spec "..."```), and (usually the same) examples with manually-constructed typeclass instances worked out while debugging the lexicon
