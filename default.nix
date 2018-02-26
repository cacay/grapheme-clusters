{ system ? builtins.currentSystem }:

let
  pkgs = import <nixpkgs> { inherit system; };

  callPackage = pkgs.lib.callPackageWith (pkgs // pkgs.xlibs // deps);

  coq = pkgs.coqPackages_8_6;

  deps = {
    # wamd = callPackage ./pkgs/wamd { };
  };
in
pkgs.stdenv.mkDerivation rec {
  name = "grapheme-clusters-${version}";
  version = "1.0.0";

  src = ".";

  # env = pkgs.buildEnv { name = name; paths = buildInputs; };

  buildInputs = [
    coq.coq
    coq.ssreflect
    # coq.mathcomp
  ];

  meta = {
    description = "Code and proofs about Unicode grapheme cluster boundary rules";
    license = pkgs.stdenv.lib.licenses.mit;
    maintainers = [ "Cosku Acay <coskuacay@gmail.com>" ];
  };
}
