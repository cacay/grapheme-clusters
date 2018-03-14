# Grapheme Clusters

A mix of Coq proofs and Haskell code about Unicode Grapheme Clusters
as specified in [UAX29](http://unicode.org/reports/tr29/#Grapheme_Cluster_Boundaries).
The idea is to automatically derive a regular expression from the rules
given in UAX29 and identify degenerate cases (since UAX29 doesn't list all
degenerate cases).


## Usage and Development

Use [Stack](https://docs.haskellstack.org).


