{ system ? builtins.currentSystem }:

let
  pkgs = import <nixpkgs> { inherit system; };

  callPackage = pkgs.lib.callPackageWith (pkgs // pkgs.xlibs // deps);

  coq = pkgs.coqPackages_8_7;

  deps = {
    coq = coq.coq;

    ssreflect = coq.ssreflect;

    regexp = callPackage ./constructive-regexp {};
  };
in
pkgs.stdenv.mkDerivation rec {
  name = "grapheme-clusters-${version}";
  version = "1.0.0";

  src = ".";

  buildInputs = [
    coq.coq
    deps.regexp
  ];

  meta = {
    description = "Code and proofs about Unicode grapheme cluster boundary rules";
    license = pkgs.stdenv.lib.licenses.mit;
    maintainers = [ "Cosku Acay <coskuacay@gmail.com>" ];
  };
}
