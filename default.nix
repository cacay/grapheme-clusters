{ system ? builtins.currentSystem }:

let
  pkgs = import <nixpkgs> { inherit system; };

  callPackage = pkgs.lib.callPackageWith (pkgs // pkgs.xlibs // deps);

  coqPackages = pkgs.coqPackages_8_5;
  coq = coqPackages.coq;

  deps = {
    # TODO: installl from nixpkgs
    relation-algebra = pkgs.stdenv.mkDerivation rec {
      name = "coq${coq.coq-version}-${repo}-${version}";
      version = "1.6";
      # version = "v8.6.0-4-g1a604fa";

      repo = "relation-algebra";

      src = pkgs.fetchFromGitHub {
        owner = "damien-pous";
        repo = "${repo}";
        rev = "d77db1594a1e57f84c3f8de360ea0827d6f3e69e";
        sha256 = "0zr70y6b681qv1ixfsjl9dsiksl2lczynr49xrd2299wfapl8ys6";
        # owner = "coq-contribs";
        # repo = "${repo}";
        # rev = "0d3ca3eb5490b2f32d5c2763e2343d373e78baea";
        # sha256 = "0scy38d5knp469p68q0zkrfy8xq83871zfc467l8639ws14y6wn0";
      };

      buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib ];

      configurePhase = "coq_makefile -f Make -o Makefile";

      installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
    };
  };
in
pkgs.stdenv.mkDerivation rec {
  name = "grapheme-clusters-${version}";
  version = "1.0.0";

  src = ".";

  buildInputs = [
    coq
    coqPackages.ssreflect
    deps.relation-algebra
  ];

  meta = {
    description = "Code and proofs about Unicode grapheme cluster boundary rules";
    license = pkgs.stdenv.lib.licenses.mit;
    maintainers = [ "Cosku Acay <coskuacay@gmail.com>" ];
  };
}
